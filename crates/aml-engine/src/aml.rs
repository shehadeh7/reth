use crate::account_profile::AccountProfile;
use alloy_primitives::{Address, U256};
use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};
use crate::aml_db::{AccountProfileDb, AmlDb};

// 100 * 1e18 = 100000000000000000000
// pub const MAX_SINGLE_TX_AMOUNT: U256 = U256::from_limbs([
//     0x6BC75E2D63100000, // Limb 0 (LSB)
//     0x5, // Limb 1
//     0x0,                 // Limb 2
//     0x0,                 // Limb 3 (MSB)
// ]);

// 1_000 * 1e18 = 1000000000000000000000
pub const DAILY_LIMIT: U256 = U256::from_limbs([
    0x35C9ADC5DEA00000,
    0x36,
    0x0,
    0x0,
]);

// 10_000 * 1e18 = 10000000000000000000000
pub const WEEKLY_LIMIT: U256 = U256::from_limbs([
    0x19E0C9BAB2400000,
    0x21E,
    0x0,
    0x0,
]);

// 100_000 * 1e18 = 100000000000000000000000
pub const MONTHLY_LIMIT: U256 = U256::from_limbs([
    0x02c7e14af6800000,
    0x152d,
    0x0,
    0x0,
]);

const MONTHLY_WINDOW_BLOCKS: u64 = 216_000; // ~30 days
const DAILY_WINDOW_BLOCKS: u64 = 7_200;   // ~1 day at 12s/block
const WEEKLY_WINDOW_BLOCKS: u64 = 50_400; // ~1 week


pub static AML_EVALUATOR: OnceLock<RwLock<AmlEvaluator>> = OnceLock::new();

pub struct AmlEvaluator {
    db: AmlDb,
    committed_profiles: HashMap<Address, AccountProfile>,
    pending_profiles: HashMap<u64, HashMap<Address, AccountProfile>>,
    finalized_block: u64,
}

impl AmlEvaluator {
    pub fn new(db: AmlDb, finalized_block: u64) -> Self {
        Self {
            db,
            committed_profiles: HashMap::new(),
            pending_profiles: HashMap::new(),
            finalized_block,
        }
    }

    fn check_compliance_internal(
        sender_profile: &AccountProfile,
        recipient_profile: &AccountProfile,
        amount: U256,
        _current_block: u64,
    ) -> Option<&'static str> {
        // if amount > MAX_SINGLE_TX_AMOUNT {
        //     return Some("single_transaction_above_threshold");
        // }

        if sender_profile.would_exceed_limits(amount, DAILY_LIMIT, WEEKLY_LIMIT, MONTHLY_LIMIT) {
            return Some("sender_limits_exceeded");
        }

        if recipient_profile.would_exceed_limits(amount, DAILY_LIMIT, WEEKLY_LIMIT, MONTHLY_LIMIT) {
            return Some("recipient_limits_exceeded");
        }

        None
    }

    fn update_profile(profile: &mut AccountProfile, block_number: u64, amount: U256) {
        profile.add_spend(block_number, amount);
    }

    pub fn check_mempool_tx(
        &mut self,
        sender: Address,
        recipient: Address,
        amount: U256,
        block_number: u64,
    ) -> (bool, Option<&'static str>) {
        if sender == recipient {
            return (true, None); // no-op
        }

        let block_profiles = self.pending_profiles.entry(block_number).or_insert_with(HashMap::new);

        // Load or create sender profile
        if !block_profiles.contains_key(&sender) {
            let sender_profile = self.committed_profiles.get(&sender).cloned()
                .or_else(|| self.db.load_profile(&sender).map(AccountProfile::from))
                .unwrap_or_else(|| AccountProfile::new(sender, block_number));
            block_profiles.insert(sender, sender_profile);
        }

        // Load or create recipient profile
        if !block_profiles.contains_key(&recipient) {
            let recipient_profile = self.committed_profiles.get(&recipient).cloned()
                .or_else(|| self.db.load_profile(&recipient).map(AccountProfile::from))
                .unwrap_or_else(|| AccountProfile::new(recipient, block_number));
            block_profiles.insert(recipient, recipient_profile);
        }

        let sender_profile = block_profiles.get(&sender).unwrap();
        let recipient_profile = block_profiles.get(&recipient).unwrap();

        let reason = Self::check_compliance_internal(sender_profile, recipient_profile, amount, block_number);

        if reason.is_some() {
            (false, reason)
        } else {
            let sender_profile = block_profiles.get_mut(&sender).unwrap();
            Self::update_profile(sender_profile, block_number, amount);
            let recipient_profile = block_profiles.get_mut(&recipient).unwrap();
            Self::update_profile(recipient_profile, block_number, amount);
            (true, None)
        }
    }

    /// Method to revert a single pending transaction from pending profiles
    pub fn revert_mempool_tx(&mut self, sender: Address, recipient: Address, amount: U256, block_number: u64) {
        if sender == recipient {
            return; // no-op
        }

        if let Some(block_profiles) = self.pending_profiles.get_mut(&block_number) {
            if let Some(sender_profile) = block_profiles.get_mut(&sender) {
                sender_profile.remove_spend(block_number, amount);
            }
            if let Some(recipient_profile) = block_profiles.get_mut(&recipient) {
                recipient_profile.remove_spend(block_number, amount);
            }
        }
    }

    pub fn check_compliance_batch(
        &self,
        transactions: &[(Address, Address, U256)],
        block_number: u64,
    ) -> Vec<(bool, Option<&'static str>)> {
        let mut temp_profiles = HashMap::new();
        let mut results = Vec::with_capacity(transactions.len());

        for &(sender, recipient, amount) in transactions {
            if sender == recipient {
                results.push((true, None));
                continue;
            }

            if !temp_profiles.contains_key(&sender) {
                let sender_profile = self.committed_profiles.get(&sender).cloned()
                    .or_else(|| self.db.load_profile(&sender).map(AccountProfile::from))
                    .unwrap_or_else(|| AccountProfile::new(sender, block_number));
                temp_profiles.insert(sender, sender_profile);
            }

            if !temp_profiles.contains_key(&recipient) {
                let recipient_profile = self.committed_profiles.get(&recipient).cloned()
                    .or_else(|| self.db.load_profile(&recipient).map(AccountProfile::from))
                    .unwrap_or_else(|| AccountProfile::new(recipient, block_number));
                temp_profiles.insert(recipient, recipient_profile);
            }

            // Get mutable profiles to apply transaction effects
            let mut sender_profile = temp_profiles.remove(&sender).unwrap();
            let mut recipient_profile = temp_profiles.remove(&recipient).unwrap();

            let reason = Self::check_compliance_internal(&sender_profile, &recipient_profile, amount, block_number);

            if reason.is_some() {
                results.push((false, reason));
            } else {
                // Apply spends for compliance check
                Self::update_profile(&mut sender_profile, block_number, amount);
                Self::update_profile(&mut recipient_profile, block_number, amount);
                // Reinsert updated profiles into temp_profiles
                temp_profiles.insert(sender, sender_profile);
                temp_profiles.insert(recipient, recipient_profile);
                results.push((true, None));
            }
        }

        results
    }

    pub fn update_profiles(
        &mut self,
        sender: Address,
        recipient: Address,
        amount: U256,
        block_number: u64,
    ) {
        if sender == recipient {
            return;
        }

        let block_profiles = self.pending_profiles.entry(block_number).or_insert_with(HashMap::new);

        // Update sender in pending_profiles
        let mut sender_profile = block_profiles.get(&sender).cloned()
            .or_else(|| self.committed_profiles.get(&sender).cloned())
            .unwrap_or_else(|| AccountProfile::new(sender, block_number));
        Self::update_profile(&mut sender_profile, block_number, amount);
        block_profiles.insert(sender, sender_profile);

        // Update recipient in pending_profiles
        let mut recipient_profile = block_profiles.get(&recipient).cloned()
            .or_else(|| self.committed_profiles.get(&recipient).cloned())
            .unwrap_or_else(|| AccountProfile::new(recipient, block_number));
        Self::update_profile(&mut recipient_profile, block_number, amount);
        block_profiles.insert(recipient, recipient_profile);
    }

    pub fn update_profiles_batch(
        &mut self,
        updates: &[(Address, Address, U256)],
        block_number: u64,
    ) {
        let block_profiles = self.pending_profiles.entry(block_number).or_insert_with(HashMap::new);

        for &(sender, recipient, amount) in updates {
            if sender == recipient {
                continue;
            }

            // Update sender
            let mut sender_profile = block_profiles.get(&sender).cloned()
                .or_else(|| self.committed_profiles.get(&sender).cloned())
                .unwrap_or_else(|| AccountProfile::new(sender, block_number));
            Self::update_profile(&mut sender_profile, block_number, amount);
            block_profiles.insert(sender, sender_profile);

            // Update recipient
            let mut recipient_profile = block_profiles.get(&recipient).cloned()
                .or_else(|| self.committed_profiles.get(&recipient).cloned())
                .unwrap_or_else(|| AccountProfile::new(recipient, block_number));
            Self::update_profile(&mut recipient_profile, block_number, amount);
            block_profiles.insert(recipient, recipient_profile);
        }
    }

    pub fn update_finalized_block(&mut self, new_finalized_block: u64) {
        if new_finalized_block <= self.finalized_block {
            return;
        }

        // Move pending profiles to committed for finalized blocks
        let finalized_range = self.finalized_block + 1..=new_finalized_block;
        let mut profiles_to_save = Vec::new();
        for block in finalized_range.clone() {
            if let Some(block_profiles) = self.pending_profiles.remove(&block) {
                for (addr, mut profile) in block_profiles {
                    profile.prune_old(new_finalized_block, MONTHLY_WINDOW_BLOCKS);
                    self.committed_profiles.insert(addr, profile.clone());
                    if !profile.spends.is_empty() {
                        profiles_to_save.push(AccountProfileDb::from(&profile));
                    } else {
                        self.db.delete_profile(&addr);
                    }
                }
            }
        }

        // Save non-empty profiles to DB
        self.db.save_profiles_batch(&profiles_to_save);

        // Clean up committed_profiles
        self.committed_profiles.retain(|addr, profile| {
            if profile.spends.is_empty() {
                self.db.delete_profile(addr);
                false
            } else {
                true
            }
        });

        self.finalized_block = new_finalized_block;
    }

    pub fn handle_reorg(&mut self, reverted_block: u64) {
        if let Some(block_profiles) = self.pending_profiles.remove(&reverted_block) {
            for (addr, mut profile) in block_profiles {
                profile.spends.remove(&reverted_block);
                profile.prune_old(self.finalized_block, MONTHLY_WINDOW_BLOCKS);
                if !profile.spends.is_empty() {
                    self.committed_profiles.insert(addr, profile);
                } else {
                    self.committed_profiles.remove(&addr);
                    self.db.delete_profile(&addr);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use alloy_primitives::{Address, U256};
    use std::time::Instant;

    fn addr(byte: u8) -> Address {
        // helper to make dummy addresses like 0x000..01, 0x000..02, etc.
        Address::repeat_byte(byte)
    }

    fn new_evaluator() -> AmlEvaluator {
        // temp dir to avoid writing to real DB
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("aml_db");
        let db = AmlDb::new(db_path.to_str().unwrap());
        AmlEvaluator::new(db, 0)
    }

    #[test]
    fn test_self_transfer_is_noop() {
        let mut aml = new_evaluator();
        let sender = addr(1);
        let amount = U256::from(1000);

        let (ok, reason) = aml.check_mempool_tx(sender, sender, amount, 1);
        assert!(ok, "Self-transfer should be allowed");
        assert!(reason.is_none(), "Self-transfer should not trigger AML checks");
    }

    #[test]
    fn test_basic_valid_transfer_updates_profiles() {
        let mut aml = new_evaluator();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(100);

        let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);
        assert!(ok, "Transfer should be allowed");
        assert!(reason.is_none(), "Transfer should pass AML checks");

        // Verify pending_profiles updated
        let block_profiles = aml.pending_profiles.get(&1).expect("Block profiles should exist");
        let sender_profile = block_profiles.get(&sender).expect("Sender profile should exist");
        let recipient_profile = block_profiles.get(&recipient).expect("Recipient profile should exist");

        assert_eq!(
            sender_profile.daily_sum, amount,
            "Sender daily_sum should match amount"
        );
        assert_eq!(
            recipient_profile.daily_sum, amount,
            "Recipient daily_sum should match amount"
        );
        assert_eq!(
            sender_profile.spends.get(&1).copied(), Some(amount),
            "Sender spends should include amount"
        );
        assert_eq!(
            recipient_profile.spends.get(&1).copied(), Some(amount),
            "Recipient spends should include amount"
        );

        // Commit to committed_profiles and DB
        aml.update_finalized_block(1);

        let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
        let recipient_profile = aml
            .committed_profiles
            .get(&recipient)
            .expect("Recipient profile should exist");

        assert_eq!(
            sender_profile.daily_sum, amount,
            "Committed sender daily_sum should match amount"
        );
        assert_eq!(
            recipient_profile.daily_sum, amount,
            "Committed recipient daily_sum should match amount"
        );
    }

    #[test]
    fn test_daily_limit_exceeded() {
        let mut aml = new_evaluator();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = DAILY_LIMIT; // 1M wei
        let extra_amount = U256::from(1);

        // First transaction: hits daily limit
        let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);
        assert!(ok, "First transfer should be allowed");
        assert!(reason.is_none(), "First transfer should pass AML checks");

        // Second transaction: exceeds daily limit
        let (ok, reason) = aml.check_mempool_tx(sender, recipient, extra_amount, 1);
        assert!(!ok, "Transfer exceeding daily limit should be rejected");
        assert_eq!(reason, Some("sender_limits_exceeded"));

        // Verify sender's daily_sum
        let block_profiles = aml.pending_profiles.get(&1).expect("Block profiles should exist");
        let sender_profile = block_profiles.get(&sender).expect("Sender profile should exist");
        assert_eq!(
            sender_profile.daily_sum, amount,
            "Sender daily_sum should match first transaction"
        );
    }

    // #[test]
    // fn test_batch_compliance_mixed_results() {
    //     let mut aml = new_evaluator();
    //     let sender = addr(1);
    //     let recipient = addr(2);
    //     let valid_amount = U256::from(10);
    //     let invalid_amount = MAX_SINGLE_TX_AMOUNT + U256::from(1);
    //
    //     // Batch with one valid and one invalid transaction
    //     let txs = vec![
    //         (sender, recipient, valid_amount),           // Valid
    //         (sender, recipient, invalid_amount),         // Invalid
    //         (sender, recipient, DAILY_LIMIT + U256::from(1)), // Exceeds daily limit
    //     ];
    //
    //     let results = aml.check_compliance_batch(&txs, 1);
    //     assert_eq!(results.len(), 3);
    //     assert_eq!(results[0], (true, None), "Valid transaction should pass");
    //     assert_eq!(
    //         results[1],
    //         (false, Some("single_transaction_above_threshold")),
    //         "Invalid transaction should fail"
    //     );
    //     assert_eq!(
    //         results[2],
    //         (false, Some("sender_limits_exceeded")),
    //         "Transaction exceeding daily limit should fail"
    //     );
    //
    //     // Verify no changes to pending_profiles
    //     assert!(
    //         !aml.pending_profiles.contains_key(&1),
    //         "Batch check should not modify pending_profiles"
    //     );
    // }

    // #[test]
    // fn test_batch_compliance_mixed_results() {
    //     let mut aml = new_evaluator();
    //     let sender = addr(1);
    //     let recipient = addr(2);
    //
    //     // Batch with one valid tx and one failing tx
    //     let txs = vec![
    //         (sender, recipient, U256::from(10)), // valid
    //         (sender, recipient, MAX_SINGLE_TX_AMOUNT + U256::from(1)), // invalid
    //     ];
    //
    //     let results = aml.check_compliance_batch(&txs, 1);
    //     assert_eq!(results.len(), 2);
    //
    //     assert_eq!(results[0], (true, None));
    //     assert_eq!(results[1], (false, Some("single_transaction_above_threshold")));
    // }

    #[test]
    fn benchmark_mempool_vs_batch() {
        let mut aml = new_evaluator();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(1);
        let num_txs = 10_000;

        // Check mempool tx one by one
        let start = Instant::now();
        for i in 0..num_txs {
            let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);
            assert!(ok, "Tx {} should pass AML", i);
            assert!(reason.is_none());
        }
        let duration_mempool = start.elapsed();
        println!(
            "check_mempool_tx: validated {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            duration_mempool,
            duration_mempool / num_txs as u32
        );

        // Check compliance batch
        let txs: Vec<(Address, Address, U256)> =
            (0..num_txs).map(|_| (sender, recipient, amount)).collect();
        let start = Instant::now();
        let results = aml.check_compliance_batch(&txs, 1);
        let duration_batch = start.elapsed();

        assert!(results.iter().all(|(ok, reason)| *ok && reason.is_none()));
        println!(
            "check_compliance_batch: validated {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            duration_batch,
            duration_batch / num_txs as u32
        );

        // Verify profile accounting
        aml.update_finalized_block(1);
        let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
        assert_eq!(
            sender_profile.daily_sum,
            U256::from(num_txs),
            "Sender daily_sum should match number of txs"
        );
        let recipient_profile = aml
            .committed_profiles
            .get(&recipient)
            .expect("Recipient profile should exist");
        assert_eq!(
            recipient_profile.daily_sum,
            U256::from(num_txs),
            "Recipient daily_sum should match number of txs"
        );
    }

    #[test]
    fn benchmark_profile_writes() {
        let mut aml = new_evaluator();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(1);
        let num_txs = 500;

        // Prepare txs
        let txs: Vec<(Address, Address, U256)> =
            (0..num_txs).map(|_| (sender, recipient, amount)).collect();

        // Benchmark write
        let start = Instant::now();
        aml.update_profiles_batch(&txs, 1);
        let elapsed = start.elapsed();

        println!(
            "update_profiles_batch: {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            elapsed,
            elapsed / num_txs as u32
        );

        // Benchmark batch compliance only
        let start = Instant::now();
        let results = aml.check_compliance_batch(&txs, 1);
        let elapsed_batch = start.elapsed();

        assert!(results.iter().all(|(ok, reason)| *ok && reason.is_none()));
        println!(
            "check_compliance_batch: {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            elapsed_batch,
            elapsed_batch / num_txs as u32
        );

        // Verify profile accounting
        aml.update_finalized_block(1);
        let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
        assert_eq!(
            sender_profile.daily_sum,
            U256::from(num_txs),
            "Sender daily_sum should match number of txs"
        );
        let recipient_profile = aml
            .committed_profiles
            .get(&recipient)
            .expect("Recipient profile should exist");
        assert_eq!(
            recipient_profile.daily_sum,
            U256::from(num_txs),
            "Recipient daily_sum should match number of txs"
        );
    }
}
