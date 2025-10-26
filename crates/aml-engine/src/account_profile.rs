use std::collections::{BTreeMap, HashMap};
use alloy_primitives::{Address, U256};
use crate::aml_rules::AmlRule;

#[derive(Debug, Clone, Default)]
pub struct BlockMetrics {
    // TODO: consider whether block metrics is actually needed vs just keeping other_address, is_sender, amount
    // Values could be computed on the fly in parallel if they're just lightweight calculations
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

// TODO: minimize this to hourly/daily since weekly/monthly requires storing a lot of data in memory
const WINDOWS: &[u64] = &[7200, 50400, 216000];  // daily, weekly, monthly assuming 12s/block

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    /// Token -> per-block metrics
    pub metrics: HashMap<Address, BTreeMap<u64, BlockMetrics>>,
    /// Token -> per-window cache
    pub caches: HashMap<Address, Vec<WindowCache>>,
    pub last_update_block: u64,
}

impl AccountProfile {
    pub fn new(address: Address, block_number: u64) -> Self {
        Self {
            address,
            // Per-token maps start empty
            metrics: HashMap::new(),
            caches: HashMap::new(),
            last_update_block: block_number,
        }
    }

    /// Advance sliding spend windows to the current block,
    /// removing expired entries and updating aggregate caches.
    pub fn advance_sliding_windows(&mut self, now: u64, windows: &[u64]) {
        if now <= self.last_update_block {
            return;
        }

        let max_window = windows.iter().max().copied().unwrap_or(216000);
        let prev_update = self.last_update_block;

        // Loop over all tokens
        for (token, token_metrics) in &mut self.metrics {
            let token_caches = self.caches.entry(*token).or_default();

            // For each window: subtract any blocks that have newly fallen out of the window
            for (i, &window) in windows.iter().enumerate() {
                let prev_start = prev_update.saturating_sub(window);
                let new_start = now.saturating_sub(window);

                if new_start > prev_start {
                    // Collect keys to avoid double borrow
                    let expired_keys: Vec<u64> = token_metrics
                        .range(prev_start..new_start)
                        .map(|(&b, _)| b)
                        .collect();

                    for b in expired_keys {
                        if let Some(m) = token_metrics.get(&b) {
                            if let Some(cache) = token_caches.get_mut(i) {
                                cache.sum = cache.sum.saturating_sub(m.spend_amount);
                                cache.inbound_sum = cache.inbound_sum.saturating_sub(m.receive_amount);
                                cache.count = cache.count.saturating_sub(m.tx_count);
                            }
                        }
                    }
                }
            }

            // Remove blocks older than the largest window
            let cutoff = now.saturating_sub(max_window);
            let to_remove: Vec<u64> = token_metrics
                .keys()
                .take_while(|&&b| b < cutoff)
                .copied()
                .collect();

            for b in to_remove {
                token_metrics.remove(&b);
            }
        }

        self.last_update_block = now;
    }

    /// Add outbound (for sender profile)
    pub fn add_outbound(&mut self, token: Address, block_number: u64, amount: U256, recipient: Address) {
        let token_metrics = self.metrics.entry(token).or_default();
        let entry = token_metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.spend_amount += amount;
        entry.tx_count += 1;

        let token_caches = self.caches.entry(token).or_insert_with(|| {
            // Initialize one WindowCache per window
            WINDOWS.iter().map(|_| WindowCache::default()).collect::<Vec<_>>()
        });

        // Incrementally update caches (if block is within windows)
        for (i, cache) in token_caches.iter_mut().enumerate() {
            let window = WINDOWS.get(i).copied().unwrap_or(0);
            if block_number >= self.last_update_block.saturating_sub(window) {
                cache.sum += amount;
                cache.count += 1;
            }
        }
    }

    /// Add inbound (for receiver profile)
    pub fn add_inbound(&mut self, token: Address, block_number: u64, amount: U256, sender: Address) {
        let token_metrics = self.metrics.entry(token).or_default();
        let entry = token_metrics.entry(block_number).or_insert_with(BlockMetrics::default);
        entry.receive_amount += amount;

        let token_caches = self.caches.entry(token).or_insert_with(|| {
            // Initialize one WindowCache per window
            WINDOWS.iter().map(|_| WindowCache::default()).collect::<Vec<_>>()
        });

        // Incrementally update caches (if block is within windows)
        for (i, cache) in token_caches.iter_mut().enumerate() {
            let window = WINDOWS.get(i).copied().unwrap_or(0);
            if block_number >= self.last_update_block.saturating_sub(window) {
                cache.inbound_sum += amount;
            }
        }
    }

    /// Remove inbound (reversible for receiver)
    pub fn remove_inbound(&mut self, token: Address, block_number: u64, amount: U256, sender: Address) {
        if let Some(token_metrics) = self.metrics.get_mut(&token) {
            if let Some(entry) = token_metrics.get_mut(&block_number) {
                entry.receive_amount = entry.receive_amount.saturating_sub(amount);

                if entry.spend_amount.is_zero() && entry.receive_amount.is_zero() && entry.tx_count == 0 {
                    token_metrics.remove(&block_number);
                }
            }

            if token_metrics.is_empty() {
                self.metrics.remove(&token);
            }
        }

        if let Some(token_caches) = self.caches.get_mut(&token) {
            for (i, cache) in token_caches.iter_mut().enumerate() {
                let window = WINDOWS[i];
                if block_number >= self.last_update_block.saturating_sub(window) {
                    cache.inbound_sum = cache.inbound_sum.saturating_sub(amount);
                }
            }
        }
    }

    /// Remove outbound (reversible for sender)
    pub fn remove_outbound(&mut self, token: Address, block_number: u64, amount: U256, recipient: Address) {
        if let Some(token_metrics) = self.metrics.get_mut(&token) {
            if let Some(entry) = token_metrics.get_mut(&block_number) {
                entry.spend_amount = entry.spend_amount.saturating_sub(amount);
                entry.tx_count = entry.tx_count.saturating_sub(1);

                // Clean up empty block metrics
                if entry.spend_amount.is_zero() && entry.receive_amount.is_zero() && entry.tx_count == 0 {
                    token_metrics.remove(&block_number);
                }
            }

            // Optionally clean up empty token map
            if token_metrics.is_empty() {
                self.metrics.remove(&token);
            }
        }

        // Subtract from caches
        if let Some(token_caches) = self.caches.get_mut(&token) {
            for (i, cache) in token_caches.iter_mut().enumerate() {
                let window = WINDOWS[i];
                if block_number >= self.last_update_block.saturating_sub(window) {
                    cache.sum = cache.sum.saturating_sub(amount);
                    cache.count = cache.count.saturating_sub(1);
                }
            }
        }
    }

    pub fn would_exceed_limits(
        &self,
        token: Address,
        new_amount: U256,
        new_recipient: Address,
        new_sender: Address,
        windows: &[u64],
        rules: &Vec<Box<dyn AmlRule>>,
        is_sender: bool,                  // Flag: true for sender profile (outbound checks), false for receiver (inbound)
    ) -> bool {
        // Get caches for this token OR default empty
        let token_caches: Vec<WindowCache> = self.caches.get(&token)
            .cloned()
            .unwrap_or_else(|| vec![WindowCache::default(); windows.len()]);

        // iterate all rules
        for rule in rules {
            if rule.would_exceed(
                &token_caches,           // pass only the relevant token's caches
                new_amount,
                new_recipient,
                new_sender,
                is_sender,
            ) {
                log::debug!("{} violated rule {}", self.address, rule.name());
                return true; // violation detected
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};
    use crate::aml_rules::{InboundSumRule, OutboundCountRule, OutboundSumRule};

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

        // Caches are now per-token, initially empty
        assert!(profile.caches.is_empty(), "Caches should be empty initially");

        assert_eq!(
            profile.last_update_block,
            block_number,
            "last_update_block should match"
        );
    }

    #[test]
    fn test_add_outbound() {
        let token = addr(0);
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let recipient = addr(2);
        profile.add_outbound(token, 20_000_000, U256::from(210_100), recipient);

        let entry = profile.metrics.get(&token).unwrap().get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(210_100), "Outbound spend amount should be added");
        assert_eq!(entry.tx_count, 1, "Tx count should be 1");
        assert_eq!(entry.receive_amount, U256::from(0), "Inbound receive should not change");

        // Add to same block (multiple txs to same recipient)
        profile.add_outbound(token, 20_000_000, U256::from(100_000), recipient);
        let entry = profile.metrics.get(&token).unwrap().get(&20_000_000).unwrap();
        assert_eq!(entry.spend_amount, U256::from(310_100), "Outbound spend should accumulate");
        assert_eq!(entry.tx_count, 2, "Tx count should be 2");

        // Check caches (all windows include this block)
        profile.advance_sliding_windows(20_000_000, WINDOWS);
        assert_eq!(profile.caches.get(&token).unwrap()[0].sum, U256::from(310_100), "Daily outbound sum should be 310_100");
        assert_eq!(profile.caches.get(&token).unwrap()[0].count, 2, "Daily count should be 2");
        assert_eq!(profile.caches.get(&token).unwrap()[1].sum, U256::from(310_100), "Weekly outbound sum should be 310_100");
        assert_eq!(profile.caches.get(&token).unwrap()[2].sum, U256::from(310_100), "Monthly outbound sum should be 310_100");
    }

    #[test]
    fn test_add_inbound() {
        let token = addr(0);
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        let sender = addr(2);
        profile.add_inbound(token, 20_000_000, U256::from(210_100), sender);

        let entry = profile.metrics.get(&token).unwrap().get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(210_100), "Inbound receive amount should be added");
        assert_eq!(entry.spend_amount, U256::from(0), "Outbound spend should not change");
        assert_eq!(entry.tx_count, 0, "Tx count unchanged for inbound");

        // Add to same block (multiple from same sender)
        profile.add_inbound(token, 20_000_000, U256::from(100_000), sender);
        let entry = profile.metrics.get(&token).unwrap().get(&20_000_000).unwrap();
        assert_eq!(entry.receive_amount, U256::from(310_100), "Inbound receive should accumulate");

        // Check caches
        profile.advance_sliding_windows(20_000_000, WINDOWS);
        assert_eq!(profile.caches.get(&token).unwrap()[0].inbound_sum, U256::from(310_100), "Daily inbound sum should be 310_100");
        assert_eq!(profile.caches.get(&token).unwrap()[1].inbound_sum, U256::from(310_100), "Weekly inbound sum should be 310_100");
        assert_eq!(profile.caches.get(&token).unwrap()[2].inbound_sum, U256::from(310_100), "Monthly inbound sum should be 310_100");
    }

    #[test]
    fn test_prune_old() {
        let token = addr(0);
        let mut profile = AccountProfile::new(addr(1), 19_600_000);
        let rec1 = addr(2);
        let rec2 = addr(3);
        let snd1 = addr(4);

        // Old outbound (outside all windows)
        profile.add_outbound(token, 19_700_000, U256::from(500_000), rec1);
        // Inside monthly/weekly, outside daily
        profile.add_outbound(token, 19_950_000, U256::from(300_000), rec2);
        // Recent outbound
        profile.add_outbound(token, 20_000_000, U256::from(210_100), rec1);
        // Recent inbound
        profile.add_inbound(token, 20_000_000, U256::from(150_000), snd1);

        profile.advance_sliding_windows(20_000_000, WINDOWS);

        let token_metrics = profile.metrics.get(&token).unwrap();

        assert!(!token_metrics.contains_key(&19_700_000), "Old block should be pruned");
        assert!(token_metrics.contains_key(&19_950_000), "Mid block should be kept");
        assert!(token_metrics.contains_key(&20_000_000), "Recent block should be kept");

        let entry_mid = token_metrics.get(&19_950_000).unwrap();
        let entry_recent = token_metrics.get(&20_000_000).unwrap();

        let token_caches = profile.caches.get(&token).unwrap();

        // Daily: Only recent
        assert_eq!(token_caches[0].sum, entry_recent.spend_amount, "Daily outbound sum should only include recent");
        assert_eq!(token_caches[0].count, entry_recent.tx_count, "Daily count should only include recent");
        assert_eq!(token_caches[0].inbound_sum, entry_recent.receive_amount, "Daily inbound sum should only include recent");

        // Weekly: Mid + recent
        assert_eq!(token_caches[1].sum, entry_mid.spend_amount + entry_recent.spend_amount, "Weekly outbound sum should include mid + recent");
        assert_eq!(token_caches[1].count, entry_mid.tx_count + entry_recent.tx_count, "Weekly count should include mid + recent");

        // Monthly: Same as weekly
        assert_eq!(token_caches[2].sum, entry_mid.spend_amount + entry_recent.spend_amount, "Monthly outbound sum should include mid + recent");
    }

    #[test]
    fn test_would_exceed_limits() {
        // High initial sender profile (outbound) - exceeds sum
        let token = addr(0);
        let mut sender_high = AccountProfile::new(addr(1), 20_000_000);
        let rec = addr(2);
        let snd = addr(3);
        sender_high.add_outbound(token, 20_000_000, U256::from(900_000), rec);
        sender_high.advance_sliding_windows(20_000_000, WINDOWS);

        let sum_limits = vec![U256::from(1_000_000), U256::from(5_000_000), U256::from(20_000_000)];  // daily/weekly/monthly outbound
        let inbound_sum_limits = vec![U256::from(600_000), U256::from(3_000_000), U256::from(10_000_000)];  // inbound (unused for sender)
        let count_limits = vec![5u32, 20u32, 100u32];  // Adjusted higher
        let unique_out_limits = vec![5usize, 20usize, 50usize];  // Adjusted higher
        let unique_in_limits = vec![5usize, 20usize, 50usize];  // Adjusted higher
        let rules: Vec<Box<dyn AmlRule>> = vec![
            Box::new(OutboundSumRule {
                limit_per_window: sum_limits.clone(),
            }),
            Box::new(OutboundCountRule {
                count_limits: count_limits.clone(),
            }),
            Box::new(InboundSumRule {
                inbound_sum_limits: inbound_sum_limits.clone(),
            }),
        ];

        let new_amount = U256::from(200_000);
        let new_rec = addr(6);  // New recipient
        let new_snd = snd;      // Existing sender

        // Should exceed daily outbound sum (sender perspective)
        assert!(sender_high.would_exceed_limits(token, new_amount, new_rec, new_snd, WINDOWS, &rules,true),
                "Should exceed daily outbound sum (900k + 200k > 1M)");

        // Non-exceed: Low initial sender profile
        let mut sender_low = AccountProfile::new(addr(1), 20_000_000);
        sender_low.add_outbound(token, 20_000_000, U256::from(50_000), rec);
        sender_low.advance_sliding_windows(20_000_000, WINDOWS);
        assert!(!sender_low.would_exceed_limits(token, new_amount, new_rec, new_snd, WINDOWS, &rules, true),
                "Should not exceed outbound with lower initial (50k + 200k < 1M daily)");

        // Test unique_out increase (add more to approach limit, new_rec makes exceed)
        let mut sender_near_limit = AccountProfile::new(addr(1), 20_000_000);
        for i in 0..4 {  // Add 4 unique recipients to make current=4
            sender_near_limit.add_outbound(token, 20_000_000, U256::from(10_000), addr(i as u8 + 2));
        }
        sender_near_limit.advance_sliding_windows(20_000_000, WINDOWS);

        // High initial receiver profile (inbound) - exceeds sum
        let mut receiver_high = AccountProfile::new(addr(4), 20_000_000);
        receiver_high.add_inbound(token, 20_000_000, U256::from(500_000), snd);
        receiver_high.advance_sliding_windows(20_000_000, WINDOWS);

        // Should exceed daily inbound sum (receiver perspective)
        assert!(receiver_high.would_exceed_limits(token, new_amount, new_rec, new_snd, WINDOWS, &rules, false),
                "Should exceed daily inbound sum (500k + 200k > 600k)");

        // Non-exceed: Low initial receiver profile
        let mut receiver_low = AccountProfile::new(addr(4), 20_000_000);
        receiver_low.add_inbound(token, 20_000_000, U256::from(50_000), snd);
        receiver_low.advance_sliding_windows(20_000_000, WINDOWS);
        assert!(!receiver_low.would_exceed_limits(token, new_amount, new_rec, new_snd, WINDOWS, &rules, false),
                "Should not exceed inbound with lower initial (50k + 200k < 600k daily)");

        // Test unique_in increase (add more to approach limit, new_snd makes exceed)
        let mut receiver_near_limit = AccountProfile::new(addr(4), 20_000_000);
        for i in 0..4 {  // Add 4 unique senders to make current=4
            receiver_near_limit.add_inbound(token, 20_000_000, U256::from(10_000), addr(i as u8 + 3));
        }
    }
}
