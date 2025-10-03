use std::collections::{BTreeMap, HashMap};
use alloy_primitives::{Address, U256};

#[derive(Debug, Clone, Default)]
pub struct BlockMetrics {
    pub spend_amount: U256,           // Outbound spend
    pub receive_amount: U256,         // Inbound receive
    pub tx_count: u32,                // Outbound count (velocity)
    pub recipients: HashMap<Address, u32>,  // Outbound fan-out (addr => count in block)
    pub senders: HashMap<Address, u32>,     // Inbound fan-in (addr => count in block)
}

#[derive(Debug, Clone, Default)]
pub struct WindowCache {
    pub sum: U256,              // Outbound sum
    pub inbound_sum: U256,      // Inbound sum
    pub count: u32,             // Outbound count
    pub unique_out: usize,      // Fan-out
    pub unique_in: usize,       // Fan-in
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
        let max_window = windows.iter().max().copied().unwrap_or(216000);
        while let Some((&block_num, _)) = self.metrics.iter().next() {
            if block_num >= now.saturating_sub(max_window) { break; }
            self.metrics.remove(&block_num);
        }

        self.last_update_block = now;
        for (i, &window) in windows.iter().enumerate() {
            let start = now.saturating_sub(window);
            self.caches[i].sum = self.sum_range(start, now, false);
            self.caches[i].inbound_sum = self.sum_range(start, now, true);
            self.caches[i].count = self.count_range(start, now);
            self.caches[i].unique_out = self.unique_range(start, now, false);
            self.caches[i].unique_in = self.unique_range(start, now, true);
        }
    }

    fn sum_range(&self, start: u64, end: u64, inbound: bool) -> U256 {
        self.metrics.range(start..=end)
            .map(|(_, m)| if inbound { m.receive_amount } else { m.spend_amount })
            .fold(U256::from(0), |acc, x| acc + x)
    }

    fn count_range(&self, start: u64, end: u64) -> u32 {
        self.metrics.range(start..=end).map(|(_, m)| m.tx_count).sum()
    }

    fn unique_range(&self, start: u64, end: u64, inbound: bool) -> usize {
        let mut unique = HashMap::new();
        for (_, m) in self.metrics.range(start..=end) {
            let map = if inbound { &m.senders } else { &m.recipients };
            for (&addr, &count) in map {
                if count > 0 { unique.insert(addr, ()); }
            }
        }
        unique.len()
    }

    /// Add outbound (for sender profile)
    pub fn add_outbound(&mut self, block_number: u64, amount: U256, recipient: Address) {
        let entry = self.metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.spend_amount += amount;
        entry.tx_count += 1;
        *entry.recipients.entry(recipient).or_insert(0) += 1;
        self.prune_old(block_number, WINDOWS);
    }

    /// Add inbound (for receiver profile)
    pub fn add_inbound(&mut self, block_number: u64, amount: U256, sender: Address) {
        let entry = self.metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.receive_amount += amount;
        *entry.senders.entry(sender).or_insert(0) += 1;
        self.prune_old(block_number, WINDOWS);
    }

    /// Remove inbound (reversible for receiver)
    pub fn remove_inbound(&mut self, block_number: u64, amount: U256, sender: Address) {
        if let Some(entry) = self.metrics.get_mut(&block_number) {
            entry.receive_amount = entry.receive_amount.saturating_sub(amount);
            if let Some(count) = entry.senders.get_mut(&sender) {
                *count = count.saturating_sub(1);
                if *count == 0 { entry.senders.remove(&sender); }
            }
            // Inline cleanup to avoid double mutable borrow
            if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 && entry.recipients.is_empty() && entry.senders.is_empty() {
                self.metrics.remove(&block_number);
            }
        }
        self.prune_old(block_number, WINDOWS);
    }

    /// Remove outbound (reversible for sender)
    pub fn remove_outbound(&mut self, block_number: u64, amount: U256, recipient: Address) {
        if let Some(entry) = self.metrics.get_mut(&block_number) {
            entry.spend_amount = entry.spend_amount.saturating_sub(amount);
            entry.tx_count = entry.tx_count.saturating_sub(1);
            if let Some(count) = entry.recipients.get_mut(&recipient) {
                *count = count.saturating_sub(1);
                if *count == 0 { entry.recipients.remove(&recipient); }
            }
            // Inline cleanup to avoid double mutable borrow
            if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 && entry.recipients.is_empty() && entry.senders.is_empty() {
                self.metrics.remove(&block_number);
            }
        }
        self.prune_old(block_number, WINDOWS);
    }

    fn cleanup_entry(&mut self, block_number: u64, entry: &BlockMetrics) {
        if entry.spend_amount == U256::from(0) && entry.receive_amount == U256::from(0) && entry.tx_count == 0 && entry.recipients.is_empty() && entry.senders.is_empty() {
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
        unique_out_limits: &[usize],      // Fan-out limits
        unique_in_limits: &[usize],       // Fan-in limits
        is_sender: bool,                  // Flag: true for sender profile (outbound checks), false for receiver (inbound)
    ) -> bool {
        for (i, &window) in windows.iter().enumerate() {
            let start = self.last_update_block.saturating_sub(window);

            if is_sender {
                // Sender: Project outbound (spend sum, tx count, unique recipients)
                let projected_sum = self.sum_range(start, self.last_update_block, false) + new_amount;
                let projected_count = self.count_range(start, self.last_update_block) + 1;
                let projected_unique_out = self.unique_range(start, self.last_update_block, false) +
                    if !self.is_unique_in_range(new_recipient, start, self.last_update_block, false) { 1 } else { 0 };

                println!("Is sender");
                println!("projected_sum {:?}, projected_count {:?}, projkected_unique_out {:?}", projected_sum, projected_count, projected_unique_out);
                println!("sum_limits {:?}", sum_limits);
                println!("unique_out {:?}", unique_out_limits);
                println!("unique_in_lit {:?}", unique_in_limits);
                println!("count_limits {:?}", count_limits);

                if projected_sum > sum_limits[i] ||
                    projected_count > count_limits[i] ||
                    projected_unique_out > unique_out_limits[i] {
                    return true;
                }
            } else {
                // Receiver: Project inbound (receive sum, unique senders)
                let projected_inbound_sum = self.sum_range(start, self.last_update_block, true) + new_amount;
                let projected_unique_in = self.unique_range(start, self.last_update_block, true) +
                    if !self.is_unique_in_range(new_sender, start, self.last_update_block, true) { 1 } else { 0 };

                println!("Is receiver");
                println!("projected_inbound_sum {:?}, projected_unique_in {:?}, ", projected_inbound_sum, projected_unique_in);
                println!("sum_limits {:?}", sum_limits);
                println!("unique_out {:?}", unique_out_limits);
                println!("unique_in_lit {:?}", unique_in_limits);
                println!("count_limits {:?}", count_limits);

                if projected_inbound_sum > inbound_sum_limits[i] ||
                    projected_unique_in > unique_in_limits[i] {
                    return true;
                }
            }
        }
        false
    }

    fn is_unique_in_range(&self, addr: Address, start: u64, end: u64, inbound: bool) -> bool {
        self.metrics.range(start..=end).any(|(_, m)| {
            let map = if inbound { &m.senders } else { &m.recipients };
            map.contains_key(&addr)
        })
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
            assert_eq!(cache.unique_out, 0, "All unique_out should be 0");
            assert_eq!(cache.unique_in, 0, "All unique_in should be 0");
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
        assert_eq!(entry.recipients.get(&recipient), Some(&1u32), "Recipient count should be 1");
        assert_eq!(entry.receive_amount, U256::from(0), "Inbound receive should not change");
        assert!(entry.senders.is_empty(), "No senders for outbound");

        // Add to same block (multiple txs to same recipient)
        profile.add_outbound(20_000_000, U256::from(100_000), recipient);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(310_100), "Outbound spend should accumulate");
        assert_eq!(entry.tx_count, 2, "Tx count should be 2");
        assert_eq!(entry.recipients.get(&recipient), Some(&2u32), "Recipient count should be 2");

        // Check caches (all windows include this block)
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].sum, U256::from(310_100), "Daily outbound sum should be 310_100");
        assert_eq!(profile.caches[0].count, 2, "Daily count should be 2");
        assert_eq!(profile.caches[0].unique_out, 1, "Daily unique_out should be 1");
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
        assert_eq!(entry.senders.get(&sender), Some(&1u32), "Sender count should be 1");
        assert_eq!(entry.spend_amount, U256::from(0), "Outbound spend should not change");
        assert!(entry.recipients.is_empty(), "No recipients for inbound");
        assert_eq!(entry.tx_count, 0, "Tx count unchanged for inbound");

        // Add to same block (multiple from same sender)
        profile.add_inbound(20_000_000, U256::from(100_000), sender);
        let entry = profile.metrics.get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(310_100), "Inbound receive should accumulate");
        assert_eq!(entry.senders.get(&sender), Some(&2u32), "Sender count should be 2");

        // Check caches
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].inbound_sum, U256::from(310_100), "Daily inbound sum should be 310_100");
        assert_eq!(profile.caches[0].unique_in, 1, "Daily unique_in should be 1");
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
        assert_eq!(entry.recipients.get(&recipient), Some(&1u32), "Recipient count should be 1 (multiples handled)");

        // Remove all
        profile.remove_outbound(20_000_000, U256::from(210_100), recipient);
        assert!(!profile.metrics.contains_key(&20_000_000), "Metrics entry should be removed");
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].sum, U256::from(0), "Daily outbound sum should be 0");
        assert_eq!(profile.caches[0].count, 0, "Daily count should be 0");
        assert_eq!(profile.caches[0].unique_out, 0, "Daily unique_out should be 0");
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
        assert_eq!(entry.senders.get(&sender), Some(&1u32), "Sender count should be 1");

        // Remove all
        profile.remove_inbound(20_000_000, U256::from(210_100), sender);
        assert!(!profile.metrics.contains_key(&20_000_000), "Metrics entry should be removed");
        profile.prune_old(20_000_000, WINDOWS);
        assert_eq!(profile.caches[0].inbound_sum, U256::from(0), "Daily inbound sum should be 0");
        assert_eq!(profile.caches[0].unique_in, 0, "Daily unique_in should be 0");
    }

    #[test]
    fn test_prune_old() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
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

        assert!(!profile.metrics.contains_key(&19_700_000), "Old block should be pruned");
        assert!(profile.metrics.contains_key(&19_950_000), "Mid block should be kept");
        assert!(profile.metrics.contains_key(&20_000_000), "Recent block should be kept");

        let entry_mid = profile.metrics.get(&19_950_000).unwrap();
        let entry_recent = profile.metrics.get(&20_000_000).unwrap();
        // Daily: Only recent
        assert_eq!(profile.caches[0].sum, entry_recent.spend_amount, "Daily outbound sum should only include recent");
        assert_eq!(profile.caches[0].count, entry_recent.tx_count, "Daily count should only include recent");
        assert_eq!(profile.caches[0].unique_out, 1, "Daily unique_out should be 1 (rec1)");
        assert_eq!(profile.caches[0].inbound_sum, entry_recent.receive_amount, "Daily inbound sum should only include recent");
        assert_eq!(profile.caches[0].unique_in, 1, "Daily unique_in should be 1 (snd1)");

        // Weekly: Mid + recent
        assert_eq!(profile.caches[1].sum, entry_mid.spend_amount + entry_recent.spend_amount, "Weekly outbound sum should include mid + recent");
        assert_eq!(profile.caches[1].count, entry_mid.tx_count + entry_recent.tx_count, "Weekly count should include mid + recent");
        assert_eq!(profile.caches[1].unique_out, 2, "Weekly unique_out should be 2 (rec1, rec2)");

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
        assert!(sender_high.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits, true),
                "Should exceed daily outbound sum (900k + 200k > 1M)");

        // Non-exceed: Low initial sender profile
        let mut sender_low = AccountProfile::new(addr(1), 20_000_000);
        sender_low.add_outbound(20_000_000, U256::from(50_000), rec);
        sender_low.prune_old(20_000_000, WINDOWS);
        assert!(!sender_low.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits, true),
                "Should not exceed outbound with lower initial (50k + 200k < 1M daily)");

        // Test unique_out increase (add more to approach limit, new_rec makes exceed)
        let mut sender_near_limit = AccountProfile::new(addr(1), 20_000_000);
        for i in 0..4 {  // Add 4 unique recipients to make current=4
            sender_near_limit.add_outbound(20_000_000, U256::from(10_000), addr(i as u8 + 2));
        }
        sender_near_limit.prune_old(20_000_000, WINDOWS);
        let unique_out_limits_tight = vec![4usize, 20usize, 50usize];  // Daily limit 4, current 4, new makes 5 >4
        assert!(sender_near_limit.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits_tight, &unique_in_limits, true),
                "Should exceed daily unique_out (new recipient increases to 5 > 4)");

        // Non-exceed unique_out (existing rec keeps 4 <=4)
        assert!(!sender_near_limit.would_exceed_limits(new_amount, rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits_tight, &unique_in_limits, true),
                "Should not exceed unique_out (existing recipient keeps 4 <= 4)");

        // High initial receiver profile (inbound) - exceeds sum
        let mut receiver_high = AccountProfile::new(addr(4), 20_000_000);
        receiver_high.add_inbound(20_000_000, U256::from(500_000), snd);
        receiver_high.prune_old(20_000_000, WINDOWS);

        // Should exceed daily inbound sum (receiver perspective)
        assert!(receiver_high.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits, false),
                "Should exceed daily inbound sum (500k + 200k > 600k)");

        // Non-exceed: Low initial receiver profile
        let mut receiver_low = AccountProfile::new(addr(4), 20_000_000);
        receiver_low.add_inbound(20_000_000, U256::from(50_000), snd);
        receiver_low.prune_old(20_000_000, WINDOWS);
        assert!(!receiver_low.would_exceed_limits(new_amount, new_rec, new_snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits, false),
                "Should not exceed inbound with lower initial (50k + 200k < 600k daily)");

        // Test unique_in increase (add more to approach limit, new_snd makes exceed)
        let mut receiver_near_limit = AccountProfile::new(addr(4), 20_000_000);
        for i in 0..4 {  // Add 4 unique senders to make current=4
            receiver_near_limit.add_inbound(20_000_000, U256::from(10_000), addr(i as u8 + 3));
        }
        receiver_near_limit.prune_old(20_000_000, WINDOWS);
        let unique_in_limits_tight = vec![4usize, 20usize, 50usize];  // Daily limit 4, current 4, new makes 5 >4
        let new_snd2 = addr(7);  // New sender
        assert!(receiver_near_limit.would_exceed_limits(new_amount, new_rec, new_snd2, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits_tight, false),
                "Should exceed daily unique_in (new sender increases to 5 > 4)");

        // Non-exceed unique_in (existing snd keeps 4 <=4)
        assert!(!receiver_near_limit.would_exceed_limits(new_amount, new_rec, snd, WINDOWS, &sum_limits, &inbound_sum_limits, &count_limits, &unique_out_limits, &unique_in_limits_tight, false),
                "Should not exceed unique_in (existing sender keeps 4 <= 4)");
    }
}
