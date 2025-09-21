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
