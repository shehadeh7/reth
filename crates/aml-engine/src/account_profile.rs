use std::collections::{BTreeMap};
use alloy_primitives::{Address, U256};

const DAILY_WINDOW_BLOCKS: u64 = 7_200;   // ~1 day at 12s/block
const WEEKLY_WINDOW_BLOCKS: u64 = 50_400; // ~1 week
const MONTHLY_WINDOW_BLOCKS: u64 = 216_000; // ~30 days

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    pub spends: BTreeMap<u64, U256>, // block_number => total spent in that block
    pub daily_sum: U256,             // Cached sum for last 7,200 blocks
    pub weekly_sum: U256,            // Cached sum for last 50,400 blocks
    pub monthly_sum: U256,           // Cached sum for last 216,000 blocks
    pub last_update_block: u64,      // Last block number this profile was updated
}

impl AccountProfile {
    pub fn new(address: Address, block_number: u64) -> Self {
        Self {
            address,
            spends: BTreeMap::new(),
            daily_sum: U256::from(0),
            weekly_sum: U256::from(0),
            monthly_sum: U256::from(0),
            last_update_block: block_number,
        }
    }

    /// Prune spends older than the specified window and recompute sums.
    pub fn prune_old(&mut self, now: u64, window: u64) {
        // Prune spends outside the window
        while let Some((&block_num, _)) = self.spends.iter().next() {
            if block_num >= now.saturating_sub(window) {
                break;
            }
            self.spends.remove(&block_num);
        }

        // Recompute cached sums
        self.last_update_block = now;
        self.monthly_sum = self.sum_range(now.saturating_sub(MONTHLY_WINDOW_BLOCKS), now);
        self.weekly_sum = self.sum_range(now.saturating_sub(WEEKLY_WINDOW_BLOCKS), now);
        self.daily_sum = self.sum_range(now.saturating_sub(DAILY_WINDOW_BLOCKS), now);
    }

    /// Sum spends in the range [start_block, end_block).
    fn sum_range(&self, start_block: u64, end_block: u64) -> U256 {
        self.spends
            .range(start_block..=end_block)
            .map(|(_, &sum)| sum)
            .fold(U256::from(0), |acc, x| acc + x)
    }

    /// Add a spend amount for a block (for new txs or block processing).
    pub fn add_spend(&mut self, block_number: u64, amount: U256) {
        self.spends
            .entry(block_number)
            .and_modify(|e| *e += amount)
            .or_insert(amount);
        self.prune_old(block_number, MONTHLY_WINDOW_BLOCKS);
    }

    /// Remove a spend amount for a block (for reorgs or tx replacements).
    pub fn remove_spend(&mut self, block_number: u64, amount: U256) {
        if let Some(entry) = self.spends.get_mut(&block_number) {
            *entry = entry.saturating_sub(amount);
            if *entry == U256::from(0) {
                self.spends.remove(&block_number);
            }
        }
        self.prune_old(block_number, MONTHLY_WINDOW_BLOCKS);
    }

    /// Check if adding a spend would exceed AML limits.
    pub fn would_exceed_limits(&self, amount: U256, daily_limit: U256, weekly_limit: U256, monthly_limit: U256) -> bool {
        self.daily_sum + amount > daily_limit ||
            self.weekly_sum + amount > weekly_limit ||
            self.monthly_sum + amount > monthly_limit
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256, FixedBytes};
    use std::collections::BTreeMap;

    const DAILY_WINDOW_BLOCKS: u64 = 7_200;   // ~1 day at 12s/block
    const WEEKLY_WINDOW_BLOCKS: u64 = 50_400; // ~1 week
    const MONTHLY_WINDOW_BLOCKS: u64 = 216_000; // ~30 days

    fn addr(byte: u8) -> Address {
        Address::repeat_byte(byte)
    }

    #[test]
    fn test_new_profile() {
        let address = addr(1);
        let block_number = 20_000_000;
        let profile = AccountProfile::new(address, block_number);

        assert_eq!(profile.address, address, "Address should match");
        assert!(profile.spends.is_empty(), "Spends should be empty");
        assert_eq!(profile.daily_sum, U256::from(0), "daily_sum should be 0");
        assert_eq!(profile.weekly_sum, U256::from(0), "weekly_sum should be 0");
        assert_eq!(profile.monthly_sum, U256::from(0), "monthly_sum should be 0");
        assert_eq!(profile.last_update_block, block_number, "last_update_block should match");
    }

    #[test]
    fn test_add_spend() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        profile.add_spend(20_000_000, U256::from(210_100));

        assert_eq!(profile.spends.get(&20_000_000), Some(&U256::from(210_100)), "Spend should be added");
        assert_eq!(profile.daily_sum, U256::from(210_100), "daily_sum should be 210_100");
        assert_eq!(profile.weekly_sum, U256::from(210_100), "weekly_sum should be 210_100");
        assert_eq!(profile.monthly_sum, U256::from(210_100), "monthly_sum should be 210_100");
        assert_eq!(profile.last_update_block, 20_000_000, "last_update_block should be 20_000_000");

        // Add to same block
        profile.add_spend(20_000_000, U256::from(100_000));
        assert_eq!(profile.spends.get(&20_000_000), Some(&U256::from(310_100)), "Spend should accumulate");
        assert_eq!(profile.daily_sum, U256::from(310_100), "daily_sum should be 310_100");
        assert_eq!(profile.weekly_sum, U256::from(310_100), "weekly_sum should be 310_100");
        assert_eq!(profile.monthly_sum, U256::from(310_100), "monthly_sum should be 310_100");
    }

    #[test]
    fn test_remove_spend() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        profile.add_spend(20_000_000, U256::from(210_100));
        profile.remove_spend(20_000_000, U256::from(100_000));

        assert_eq!(profile.spends.get(&20_000_000), Some(&U256::from(110_100)), "Spend should be reduced");
        assert_eq!(profile.daily_sum, U256::from(110_100), "daily_sum should be 110_100");
        assert_eq!(profile.weekly_sum, U256::from(110_100), "weekly_sum should be 110_100");
        assert_eq!(profile.monthly_sum, U256::from(110_100), "monthly_sum should be 110_100");

        // Remove all spend
        profile.remove_spend(20_000_000, U256::from(110_100));
        assert!(!profile.spends.contains_key(&20_000_000), "Spend should be removed");
        assert_eq!(profile.daily_sum, U256::from(0), "daily_sum should be 0");
        assert_eq!(profile.weekly_sum, U256::from(0), "weekly_sum should be 0");
        assert_eq!(profile.monthly_sum, U256::from(0), "monthly_sum should be 0");
    }

    #[test]
    fn test_prune_old() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        profile.spends.insert(19_700_000, U256::from(500_000)); // Outside monthly window
        profile.spends.insert(19_950_000, U256::from(300_000)); // Inside monthly, outside daily/weekly
        profile.spends.insert(20_000_000, U256::from(210_100)); // Recent
        profile.prune_old(20_000_000, MONTHLY_WINDOW_BLOCKS);

        assert!(!profile.spends.contains_key(&19_700_000), "Spend at 19_700_000 should be pruned");
        assert!(profile.spends.contains_key(&19_950_000), "Spend at 19_950_000 should be kept");
        assert!(profile.spends.contains_key(&20_000_000), "Spend at 20_000_000 should be kept");
        assert_eq!(
            profile.daily_sum,
            U256::from(210_100),
            "daily_sum should be 210_100 (only block 20_000_000)"
        );
        assert_eq!(
            profile.weekly_sum,
            U256::from(510_100),
            "weekly_sum should be 510_100 (blocks 19_950_000 + 20_000_000)"
        );
        assert_eq!(
            profile.monthly_sum,
            U256::from(510_100),
            "monthly_sum should be 510_100 (blocks 19_950_000 + 20_000_000)"
        );
        assert_eq!(profile.last_update_block, 20_000_000, "last_update_block should be 20_000_000");
    }

    #[test]
    fn test_would_exceed_limits() {
        let mut profile = AccountProfile::new(addr(1), 20_000_000);
        profile.spends.insert(20_000_000, U256::from(900_000));
        profile.daily_sum = U256::from(900_000);
        profile.weekly_sum = U256::from(900_000);
        profile.monthly_sum = U256::from(900_000);

        let daily_limit = U256::from(1_000_000);
        let weekly_limit = U256::from(5_000_000);
        let monthly_limit = U256::from(20_000_000);

        // Should not exceed
        assert!(!profile.would_exceed_limits(U256::from(99_999), daily_limit, weekly_limit, monthly_limit),
                "Adding 99_999 should not exceed limits");

        // Should exceed daily limit
        assert!(profile.would_exceed_limits(U256::from(100_001), daily_limit, weekly_limit, monthly_limit),
                "Adding 100_001 should exceed daily limit");

        // Should exceed weekly limit
        profile.weekly_sum = U256::from(4_900_000);
        assert!(profile.would_exceed_limits(U256::from(200_000), daily_limit, weekly_limit, monthly_limit),
                "Adding 200_000 should exceed weekly limit");

        // Should exceed monthly limit
        profile.monthly_sum = U256::from(19_900_000);
        assert!(profile.would_exceed_limits(U256::from(200_000), daily_limit, weekly_limit, monthly_limit),
                "Adding 200_000 should exceed monthly limit");
    }
}
