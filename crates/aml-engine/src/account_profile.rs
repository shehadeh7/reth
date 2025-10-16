use std::collections::{BTreeMap};
use alloy_primitives::{Address, U256};

#[derive(Debug, Clone, Default)]
pub struct BlockMetrics {
    pub spend_amount: U256,           // Outbound spend
    pub receive_amount: U256,         // Inbound receive
    pub tx_count: u32,                // Outbound count (velocity)
}

#[derive(Debug, Clone, Default)]
pub struct WindowCache {
    pub sum: U256,              // Outbound sum
    pub inbound_sum: U256,      // Inbound sum
    pub count: u32,             // Outbound count
}

const WINDOWS: &[u64] = &[7200, 50400, 216000];  // daily, weekly, monthly assuming 12s/block

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    pub metrics: BTreeMap<u64, BlockMetrics>,
    pub caches: Vec<WindowCache>,
    pub last_update_block: u64,
}

impl AccountProfile {
    pub fn new(address: Address, block_number: u64) -> Self {
        Self {
            address,
            metrics: BTreeMap::new(),
            caches: vec![WindowCache::default(); WINDOWS.len()],  // One per window
            last_update_block: block_number,
        }
    }

    /// Prune spends older than the specified window and recompute sums.
    pub fn prune_old(&mut self, now: u64, windows: &[u64]) {
        if now <= self.last_update_block {
            return;
        }

        let max_window = windows.iter().max().copied().unwrap_or(216000);
        let prev_update = self.last_update_block;

        // For each window: subtract any blocks that have newly fallen out of the window
        for (i, &window) in windows.iter().enumerate() {
            // previous and new window starts (inclusive)
            let prev_start = prev_update.saturating_sub(window);
            let new_start = now.saturating_sub(window);

            // If window moved forward, blocks in [prev_start, new_start) fell out
            if new_start > prev_start {
                // Collect keys in the small range to avoid double borrowing
                let expired_keys: Vec<u64> = self
                    .metrics
                    .range(prev_start..new_start)
                    .map(|(&b, _)| b)
                    .collect();

                for b in expired_keys {
                    if let Some(m) = self.metrics.get(&b) {
                        let cache = &mut self.caches[i];
                        cache.sum = cache.sum.saturating_sub(m.spend_amount);
                        cache.inbound_sum = cache.inbound_sum.saturating_sub(m.receive_amount);
                        cache.count = cache.count.saturating_sub(m.tx_count);
                    }
                }
            }
        }

        // Finally remove blocks older than the largest window (they are now irrelevant to all windows)
        let cutoff = now.saturating_sub(max_window);
        let to_remove: Vec<u64> = self
            .metrics
            .keys()
            .take_while(|&&b| b < cutoff)
            .copied()
            .collect();

        for b in to_remove {
            self.metrics.remove(&b);
        }

        self.last_update_block = now;
    }

    fn sum_range(&self, start: u64, end: u64, inbound: bool) -> U256 {
        self.metrics.range(start..=end)
            .map(|(_, m)| if inbound { m.receive_amount } else { m.spend_amount })
            .fold(U256::from(0), |acc, x| acc + x)
    }

    fn count_range(&self, start: u64, end: u64) -> u32 {
        self.metrics.range(start..=end).map(|(_, m)| m.tx_count).sum()
    }

    /// Add outbound (for sender profile)
    pub fn add_outbound(&mut self, block_number: u64, amount: U256, recipient: Address) {
        let entry = self.metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.spend_amount += amount;
        entry.tx_count += 1;

        // Incrementally update caches (if block is within windows)
        for (i, &window) in WINDOWS.iter().enumerate() {
            if block_number >= self.last_update_block.saturating_sub(window) {
                let cache = &mut self.caches[i];
                cache.sum += amount;
                cache.count += 1;
            }
        }
    }

    /// Add inbound (for receiver profile)
    pub fn add_inbound(&mut self, block_number: u64, amount: U256, sender: Address) {
        let entry = self.metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.receive_amount += amount;

        for (i, &window) in WINDOWS.iter().enumerate() {
            if block_number >= self.last_update_block.saturating_sub(window) {
                let cache = &mut self.caches[i];
                cache.inbound_sum += amount;
            }
        }
    }

    /// Remove inbound (reversible for receiver)
    pub fn remove_inbound(&mut self, block_number: u64, amount: U256, sender: Address) {
        if let Some(entry) = self.metrics.get_mut(&block_number) {
            entry.receive_amount = entry.receive_amount.saturating_sub(amount);

            // Inline cleanup to avoid double mutable borrow
            if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 {
                self.metrics.remove(&block_number);
            }
        }

        // Subtract from caches
        for (i, &window) in WINDOWS.iter().enumerate() {
            if block_number >= self.last_update_block.saturating_sub(window) {
                let cache = &mut self.caches[i];
                cache.inbound_sum = cache.inbound_sum.saturating_sub(amount);
            }
        }
    }

    /// Remove outbound (reversible for sender)
    pub fn remove_outbound(&mut self, block_number: u64, amount: U256, recipient: Address) {
        if let Some(entry) = self.metrics.get_mut(&block_number) {
            entry.spend_amount = entry.spend_amount.saturating_sub(amount);
            entry.tx_count = entry.tx_count.saturating_sub(1);

            // Inline cleanup to avoid double mutable borrow
            if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 {
                self.metrics.remove(&block_number);
            }
        }

        // Subtract from caches
        for (i, &window) in WINDOWS.iter().enumerate() {
            if block_number >= self.last_update_block.saturating_sub(window) {
                let cache = &mut self.caches[i];
                cache.sum = cache.sum.saturating_sub(amount);
                cache.count = cache.count.saturating_sub(1);
            }
        }
    }

    fn cleanup_entry(&mut self, block_number: u64, entry: &BlockMetrics) {
        if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 {
            self.metrics.remove(&block_number);
        }
    }

    pub fn would_exceed_limits(
        &self,
        new_amount: U256,
        new_recipient: Address,
        new_sender: Address,
        windows: &[u64],
        sum_limits: &[U256],              // Outbound sum limits
        inbound_sum_limits: &[U256],      // Inbound sum limits
        count_limits: &[u32],             // Outbound count limits (tx count)
        is_sender: bool,                  // Flag: true for sender profile (outbound checks), false for receiver (inbound)
    ) -> bool {
        for (i, _window) in windows.iter().enumerate() {
            let cache = &self.caches[i];

            if is_sender {
                // Projected values for sender
                let projected_sum = cache.sum + new_amount;
                let projected_count = cache.count + 1;

                if projected_sum > sum_limits[i] ||
                    projected_count > count_limits[i] {
                    return true;
                }
            } else {
                // Receiver projection
                let projected_inbound_sum = cache.inbound_sum + new_amount;

                if projected_inbound_sum > inbound_sum_limits[i] {
                    return true;
                }
            }
        }
        false
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};

    const WINDOWS: &[u64] = &[7200, 50400, 216000];  // daily, weekly, monthly

    fn addr(byte: u8) -> Address {
        Address::repeat_byte(byte)
    }

    #[test]
    fn test_new_profile() {
        let address = addr(1);
        let block_number = 20_000_000;
        let profile = AccountProfile::new(address, block_number);

        assert_eq!(profile.address, address, "Address should match");
        assert!(profile.metrics.is_empty(), "Metrics should be empty");
        assert_eq!(profile.caches.len(), WINDOWS.len(), "Caches should match window count");
        for cache in &profile.caches {
            assert_eq!(cache.sum, U256::from(0), "All outbound sums should be 0");
            assert_eq!(cache.inbound_sum, U256::from(0), "All inbound sums should be 0");
            assert_eq!(cache.count, 0, "All counts should be 0");
        }
        assert_eq!(profile.last_update_block, block_number, "last_update_block should match");
    }

    #[test]
    fn test_add_outbound() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let recipient = addr(2);
        profile.add_outbound(20_000_000, U256::from(210_100), recipient);

        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(210_100), "Outbound spend amount should be added");
        assert_eq!(entry.tx_count, 1, "Tx count should be 1");
        assert_eq!(entry.receive_amount, U256::from(0), "Inbound receive should not change");

        // Add to same block (multiple txs to same recipient)
        profile.add_outbound(20_000_000, U256::from(100_000), recipient);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(310_100), "Outbound spend should accumulate");
        assert_eq!(entry.tx_count, 2, "Tx count should be 2");

        // Check caches (all windows include this block)
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].sum, U256::from(310_100), "Daily outbound sum should be 310_100");
        assert_eq!(profile.caches[0].count, 2, "Daily count should be 2");
        assert_eq!(profile.caches[1].sum, U256::from(310_100), "Weekly outbound sum should be 310_100");
        assert_eq!(profile.caches[2].sum, U256::from(310_100), "Monthly outbound sum should be 310_100");
    }

    #[test]
    fn test_add_inbound() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let sender = addr(2);
        profile.add_inbound(20_000_000, U256::from(210_100), sender);

        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(210_100), "Inbound receive amount should be added");
        assert_eq!(entry.spend_amount, U256::from(0), "Outbound spend should not change");
        assert_eq!(entry.tx_count, 0, "Tx count unchanged for inbound");

        // Add to same block (multiple from same sender)
        profile.add_inbound(20_000_000, U256::from(100_000), sender);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(310_100), "Inbound receive should accumulate");

        // Check caches
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].inbound_sum, U256::from(310_100), "Daily inbound sum should be 310_100");
        assert_eq!(profile.caches[1].inbound_sum, U256::from(310_100), "Weekly inbound sum should be 310_100");
        assert_eq!(profile.caches[2].inbound_sum, U256::from(310_100), "Monthly inbound sum should be 310_100");
    }

    #[test]
    fn test_remove_outbound() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let recipient = addr(2);
        profile.add_outbound(20_000_000, U256::from(210_100), recipient);
        profile.add_outbound(20_000_000, U256::from(100_000), recipient);  // Multiple to same

        profile.remove_outbound(20_000_000, U256::from(100_000), recipient);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(210_100), "Outbound spend should be reduced");
        assert_eq!(entry.tx_count, 1, "Tx count should be 1");

        // Remove all
        profile.remove_outbound(20_000_000, U256::from(210_100), recipient);
        assert!(!profile.metrics.contains_key(&20_000_000), "Metrics entry should be removed");
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].sum, U256::from(0), "Daily outbound sum should be 0");
        assert_eq!(profile.caches[0].count, 0, "Daily count should be 0");
    }

    #[test]
    fn test_remove_inbound() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let sender = addr(2);
        profile.add_inbound(20_000_000, U256::from(210_100), sender);
        profile.add_inbound(20_000_000, U256::from(100_000), sender);  // Multiple from same

        profile.remove_inbound(20_000_000, U256::from(100_000), sender);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(210_100), "Inbound receive should be reduced");

        // Remove all
        profile.remove_inbound(20_000_000, U256::from(210_100), sender);
        assert!(!profile.metrics.contains_key(&20_000_000), "Metrics entry should be removed");
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].inbound_sum, U256::from(0), "Daily inbound sum should be 0");
    }

    #[test]
    fn test_prune_old() {
        let mut profile = AccountProfile::new(addr(1), 19_600_000);
        let rec1 = addr(2);
        let rec2 = addr(3);
        let snd1 = addr(4);

        // Old outbound (outside all windows)
        profile.add_outbound(19_700_000, U256::from(500_000), rec1);
        // Inside monthly/weekly, outside daily
        profile.add_outbound(19_950_000, U256::from(300_000), rec2);
        // Recent outbound
        profile.add_outbound(20_000_000, U256::from(210_100), rec1);
        // Recent inbound
        profile.add_inbound(20_000_000, U256::from(150_000), snd1);

        profile.prune_old(20_000_000, WINDOWS);

        println!("profile is {:?}", profile);

        assert!(!profile.metrics.contains_key(&19_700_000), "Old block should be pruned");
        assert!(profile.metrics.contains_key(&19_950_000), "Mid block should be kept");
        assert!(profile.metrics.contains_key(&20_000_000), "Recent block should be kept");

        let entry_mid = profile.metrics.get(&19_950_000).unwrap();
        let entry_recent = profile.metrics.get(&20_000_000).unwrap();
        // Daily: Only recent
        assert_eq!(profile.caches[0].sum, entry_recent.spend_amount, "Daily outbound sum should only include recent");
        assert_eq!(profile.caches[0].count, entry_recent.tx_count, "Daily count should only include recent");
        assert_eq!(profile.caches[0].inbound_sum, entry_recent.receive_amount, "Daily inbound sum should only include recent");

        // Weekly: Mid + recent
        assert_eq!(profile.caches[1].sum, entry_mid.spend_amount + entry_recent.spend_amount, "Weekly outbound sum should include mid + recent");
        assert_eq!(profile.caches[1].count, entry_mid.tx_count + entry_recent.tx_count, "Weekly count should include mid + recent");

        // Monthly: Same as weekly
        assert_eq!(profile.caches[2].sum, entry_mid.spend_amount + entry_recent.spend_amount, "Monthly outbound sum should include mid + recent");
    }

    #[test]
    fn test_would_exceed_limits() {
        // High initial sender profile (outbound) - exceeds sum
        let mut sender_high = AccountProfile::new(addr(1), 20_000_000);
        let rec = addr(2);
        let snd = addr(3);
        sender_high.add_outbound(20_000_000, U256::from(900_000), rec);
        sender_high.prune_old(20_000_000, WINDOWS);

        let sum_limits = vec![U256::from(1_000_000), U256::from(5_000_000), U256::from(20_000_000)];  // daily/weekly/monthly outbound
        let inbound_sum_limits = vec![U256::from(600_000), U256::from(3_000_000), U256::from(10_000_000)];  // inbound (unused for sender)
        let count_limits = vec![5u32, 20u32, 100u32];  // Adjusted higher
        let unique_out_limits = vec![5usize, 20usize, 50usize];  // Adjusted higher
        let unique_in_limits = vec![5usize, 20usize, 50usize];  // Adjusted higher

        let new_amount = U256::from(200_000);
        let new_rec = addr(6);  // New recipient
        let new_snd = snd;      // Existing sender

        // Should exceed daily outbound sum (sender perspective)
        assert!(sender_high.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits,true),
                "Should exceed daily outbound sum (900k + 200k > 1M)");

        // Non-exceed: Low initial sender profile
        let mut sender_low = AccountProfile::new(addr(1), 20_000_000);
        sender_low.add_outbound(20_000_000, U256::from(50_000), rec);
        sender_low.prune_old(20_000_000, WINDOWS);
        assert!(!sender_low.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, true),
                "Should not exceed outbound with lower initial (50k + 200k < 1M daily)");

        // Test unique_out increase (add more to approach limit, new_rec makes exceed)
        let mut sender_near_limit = AccountProfile::new(addr(1), 20_000_000);
        for i in 0..4 {  // Add 4 unique recipients to make current=4
            sender_near_limit.add_outbound(20_000_000, U256::from(10_000), addr(i as u8 + 2));
        }
        sender_near_limit.prune_old(20_000_000, WINDOWS);

        // High initial receiver profile (inbound) - exceeds sum
        let mut receiver_high = AccountProfile::new(addr(4), 20_000_000);
        receiver_high.add_inbound(20_000_000, U256::from(500_000), snd);
        receiver_high.prune_old(20_000_000, WINDOWS);

        // Should exceed daily inbound sum (receiver perspective)
        assert!(receiver_high.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, false),
                "Should exceed daily inbound sum (500k + 200k > 600k)");

        // Non-exceed: Low initial receiver profile
        let mut receiver_low = AccountProfile::new(addr(4), 20_000_000);
        receiver_low.add_inbound(20_000_000, U256::from(50_000), snd);
        receiver_low.prune_old(20_000_000, WINDOWS);
        assert!(!receiver_low.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, false),
                "Should not exceed inbound with lower initial (50k + 200k < 600k daily)");

        // Test unique_in increase (add more to approach limit, new_snd makes exceed)
        let mut receiver_near_limit = AccountProfile::new(addr(4), 20_000_000);
        for i in 0..4 {  // Add 4 unique senders to make current=4
            receiver_near_limit.add_inbound(20_000_000, U256::from(10_000), addr(i as u8 + 3));
        }
    }
}
