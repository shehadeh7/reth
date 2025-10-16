use crate::account_profile::{AccountProfile, BlockMetrics};
use alloy_primitives::{Address, U256};
use std::collections::{HashMap, HashSet};
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
const WINDOWS: &[u64] = &[7200, 50400, 216000];  // daily, weekly, monthly assuming 12s/block


pub static AML_EVALUATOR: OnceLock<RwLock<AmlEvaluator>> = OnceLock::new();

pub struct AmlEvaluator {
    db: AmlDb,
    latest_profiles: HashMap<Address, AccountProfile>, // Latest Profiles (Modify to LRU if needed)
    pending_deltas: HashMap<u64, HashMap<Address, BlockMetrics>>, // Deltas for unfinalized blocks
    mempool_profiles: HashMap<Address, AccountProfile>,
    finalized_block: u64,
    current_mempool_block: Option<u64>,
}

impl AmlEvaluator {
    pub fn new(db: AmlDb, finalized_block: u64) -> Self {
        Self {
            db,
            latest_profiles: HashMap::new(),
            pending_deltas: HashMap::new(),
            mempool_profiles: HashMap::new(),
            finalized_block,
            current_mempool_block: None,
        }
    }

    fn check_compliance_internal(
        sender_profile: &AccountProfile,
        recipient_profile: &AccountProfile,
        amount: U256,
        _current_block: u64,
    ) -> Option<&'static str> {
        let sum_limits = vec![DAILY_LIMIT, WEEKLY_LIMIT, MONTHLY_LIMIT];  // daily/weekly/monthly outbound
        let inbound_sum_limits = vec![DAILY_LIMIT.saturating_add(DAILY_LIMIT), WEEKLY_LIMIT.saturating_add(WEEKLY_LIMIT), MONTHLY_LIMIT.saturating_add(MONTHLY_LIMIT)];  // inbound (unused for sender)
        let count_limits = vec![10u32, 20u32, 100u32];  // Adjusted higher


        if sender_profile.would_exceed_limits(
            amount,
            recipient_profile.address,
            sender_profile.address,
            WINDOWS,
            &sum_limits,
            &inbound_sum_limits,
            &count_limits,
            true
        )  { return Some("sender_limits_exceeded") };

        if recipient_profile.would_exceed_limits(
            amount,
            recipient_profile.address,
            sender_profile.address,
            WINDOWS,
            &sum_limits,
            &inbound_sum_limits,
            &count_limits,
            false
        ) { return Some("recipient_limits_exceeded") }

        None
    }

    fn update_recipient_profile(profile: &mut AccountProfile, block_number: u64, sender: Address, amount: U256) {
        profile.add_inbound(block_number, amount, sender);
    }

    fn update_sender_profile(profile: &mut AccountProfile, block_number: u64, recipient: Address, amount: U256) {
        profile.add_outbound(block_number, amount, recipient);
    }

    pub fn fetch_profile(&mut self, addr: Address, block_number: u64) -> AccountProfile {
        // Check latest_profiles first
        if let Some(mut profile) = self.latest_profiles.get(&addr).cloned() {
            if profile.last_update_block >= block_number.saturating_sub(1) {
                return profile;
            }
            // Profile is stale, prune to current tip
            profile.prune_old(block_number.saturating_sub(1), WINDOWS);
            self.latest_profiles.insert(addr, profile.clone());
            return profile;
        }

        // No profile in latest_profiles, load from DB or create new
        let mut profile = self.db.load_profile(&addr)
            .map(AccountProfile::from)
            .unwrap_or_else(|| AccountProfile::new(addr, self.finalized_block));

        // Apply pending deltas up to block_number - 1
        for b in profile.last_update_block + 1..block_number {
            if let Some(block_deltas) = self.pending_deltas.get(&b) {
                if let Some(delta) = block_deltas.get(&addr) {
                    profile.metrics.insert(b, delta.clone());
                }
            }
        }
        profile.prune_old(block_number.saturating_sub(1), WINDOWS);

        // Ensure last_update_block is current
        if profile.last_update_block < block_number.saturating_sub(1) {
            profile.prune_old(block_number.saturating_sub(1), WINDOWS);
        }

        // Cache in latest_profiles
        self.latest_profiles.insert(addr, profile.clone());
        profile
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

        // Reset mempool_profiles if block number changes
        if self.current_mempool_block != Some(block_number) {
            self.mempool_profiles.clear();
            self.current_mempool_block = Some(block_number);
        }

        // Load sender profile
        let mut sender_profile = self.mempool_profiles.get(&sender).cloned()
            .unwrap_or_else(|| self.fetch_profile(sender, block_number));

        // Load recipient profile
        let mut recipient_profile = self.mempool_profiles.get(&recipient).cloned()
            .unwrap_or_else(|| self.fetch_profile(recipient, block_number));

        let reason = Self::check_compliance_internal(&sender_profile, &recipient_profile, amount, block_number);

        if reason.is_none() {
            Self::update_sender_profile(&mut sender_profile, block_number, recipient, amount);
            Self::update_recipient_profile(&mut recipient_profile, block_number, sender, amount);
            // Update mempool_profiles for compliant transactions
            self.mempool_profiles.insert(sender, sender_profile);
            self.mempool_profiles.insert(recipient, recipient_profile);
        }

        (reason.is_none(), reason)
    }

    pub fn check_compliance_batch(
        &mut self,
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
                let sender_profile = self.fetch_profile(sender, block_number);
                temp_profiles.insert(sender, sender_profile);
            }

            if !temp_profiles.contains_key(&recipient) {
                let recipient_profile = self.fetch_profile(recipient, block_number);
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
                Self::update_sender_profile(&mut sender_profile, block_number, recipient, amount);
                Self::update_recipient_profile(&mut recipient_profile, block_number, sender, amount);
                // Reinsert updated profiles into temp_profiles
                temp_profiles.insert(sender, sender_profile);
                temp_profiles.insert(recipient, recipient_profile);
                results.push((true, None));
            }
        }

        results
    }

    pub fn update_profiles_batch(
        &mut self,
        updates: &[(Address, Address, U256)],
        block_number: u64,
    ) {

        if updates.is_empty() {
            return;
        }

        // block number isn't known yet, this just returns an empty map every time
        let mut block_deltas = self
            .pending_deltas
            .remove(&block_number)
            .unwrap_or_default();

        for &(sender, recipient, amount) in updates {
            if sender == recipient {
                continue;
            }

            // --- Sender ---
            let mut sender_profile = self.fetch_profile(sender, block_number);
            Self::update_sender_profile(&mut sender_profile, block_number, recipient, amount);
            if let Some(sender_metrics) = sender_profile.metrics.get(&block_number) {
                block_deltas.insert(sender, sender_metrics.clone());
            }
            self.latest_profiles.insert(sender, sender_profile);

            // --- Recipient ---
            let mut recipient_profile = self.fetch_profile(recipient, block_number);
            Self::update_recipient_profile(&mut recipient_profile, block_number, sender, amount);
            if let Some(recipient_metrics) = recipient_profile.metrics.get(&block_number) {
                block_deltas.insert(recipient, recipient_metrics.clone());
            }
            self.latest_profiles.insert(recipient, recipient_profile);
        }

        // Put the updated block deltas back
        if !block_deltas.is_empty() {
            self.pending_deltas.insert(block_number, block_deltas);
        }
    }

    pub fn update_finalized_block(&mut self, new_finalized_block: u64) {
        if new_finalized_block <= self.finalized_block {
            return;
        }

        // Collect affected addresses and deltas in the finalized range
        let finalized_range = self.finalized_block + 1..=new_finalized_block;
        let mut affected_addresses = HashSet::new();
        let mut finalized_deltas = HashMap::new();
        for block in finalized_range.clone() {
            if let Some(block_deltas) = self.pending_deltas.remove(&block) {
                affected_addresses.extend(block_deltas.keys().copied());
                finalized_deltas.insert(block, block_deltas);
            }
        }

        // Update profiles for affected addresses
        let mut profiles_to_save = Vec::new();
        for addr in &affected_addresses {
            // Load from DB or create new
            let mut profile = self.db.load_profile(addr)
                .map(AccountProfile::from)
                .unwrap_or_else(|| AccountProfile::new(*addr, self.finalized_block));

            // Apply finalized deltas up to new_finalized_block
            for (block_num, deltas) in finalized_deltas.iter() {
                if let Some(delta) = deltas.get(addr) {
                    profile.metrics.insert(*block_num, delta.clone());
                }
            }

            // Prune and prepare for save
            profile.prune_old(new_finalized_block, WINDOWS);
            if !profile.metrics.is_empty() {
                profiles_to_save.push(AccountProfileDb::from(&profile));
            } else {
                self.db.delete_profile(addr);
            }
        }

        // Save non-empty profiles to DB
        self.db.save_profiles_batch(&profiles_to_save);

        // Update finalized block
        self.finalized_block = new_finalized_block;
    }

    /// Assume reorgs never go past the finalized block
    pub fn handle_reorg(
        &mut self,
        old_blocks: &[(u64, Vec<(Address, Address, U256)>)],
        new_blocks: &[(u64, Vec<(Address, Address, U256)>)],
    ) {
        for block in old_blocks {
            if let Some(block_deltas) = self.pending_deltas.remove(&block.0) {
                for (addr, _) in block_deltas {
                    if let Some(mut profile) = self.latest_profiles.get(&addr).cloned() {
                        profile.metrics.remove(&block.0);
                        self.latest_profiles.insert(addr, profile);
                    }
                }
            }
        }

        for block in new_blocks {
            self.update_profiles_batch(&block.1, block.0);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use alloy_primitives::{Address, U256};

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
    fn test_mempool_tx_basic() {
        let mut evaluator = new_evaluator();

        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(100);
        let block_number = 1;

        // --- compliant transaction ---
        let (ok, reason) = evaluator.check_mempool_tx(sender, recipient, amount, block_number);

        assert!(ok, "Transaction should be compliant");
        assert!(reason.is_none(), "No reason for rejection");

        // Profiles should now exist in mempool_profiles
        assert!(evaluator.mempool_profiles.contains_key(&sender));
        assert!(evaluator.mempool_profiles.contains_key(&recipient));

        let sender_profile = evaluator.mempool_profiles.get(&sender).unwrap();
        let recipient_profile = evaluator.mempool_profiles.get(&recipient).unwrap();

        assert_eq!(sender_profile.metrics.get(&block_number).unwrap().spend_amount, amount);
        assert_eq!(recipient_profile.metrics.get(&block_number).unwrap().receive_amount, amount);

        // --- self-transfer ---
        let (ok, reason) = evaluator.check_mempool_tx(sender, sender, U256::from(50), block_number);
        assert!(ok);
        assert!(reason.is_none(), "Self-transfer should be no-op");

        // --- block number change resets mempool ---
        let new_block_number = 2;
        let sender2 = addr(3);
        let recipient2 = addr(4);
        let amount2 = U256::from(200);

        let (ok, reason) = evaluator.check_mempool_tx(sender2, recipient2, amount2, new_block_number);
        assert!(ok);
        assert!(reason.is_none());

        // mempool_profiles should have been reset, only new addresses exist
        assert_eq!(evaluator.mempool_profiles.len(), 2);
        assert!(evaluator.mempool_profiles.contains_key(&sender2));
        assert!(evaluator.mempool_profiles.contains_key(&recipient2));
        assert!(!evaluator.mempool_profiles.contains_key(&sender));
        assert!(!evaluator.mempool_profiles.contains_key(&recipient));
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
    fn test_non_compliant_tx() {
        let mut evaluator = new_evaluator();

        let sender = addr(1);
        let recipient = addr(2);
        let amount = DAILY_LIMIT.saturating_add(U256::from(100));
        let block_number = 1;

        let (ok, reason) = evaluator.check_mempool_tx(sender, recipient, amount, block_number);

        assert!(!ok, "Transaction should be rejected");
        assert_eq!(reason, Some("sender_limits_exceeded"));

        // mempool_profiles should not be updated
        assert!(!evaluator.mempool_profiles.contains_key(&sender));
        assert!(!evaluator.mempool_profiles.contains_key(&recipient));
    }

    #[test]
    fn test_update_profiles_batch_basic() {
        let mut evaluator = new_evaluator();

        let sender = addr(1);
        let recipient = addr(2);

        let txs = vec![(sender, recipient, U256::from(100u64))];
        let block_number = 42;

        // Call the method
        evaluator.update_profiles_batch(&txs, block_number);

        // --- Check latest_profiles ---
        let sender_profile = evaluator.latest_profiles.get(&sender).unwrap();
        let recipient_profile = evaluator.latest_profiles.get(&recipient).unwrap();

        assert!(sender_profile.metrics.contains_key(&block_number), "Sender metrics not updated");
        assert!(recipient_profile.metrics.contains_key(&block_number), "Recipient metrics not updated");

        let sender_metrics = sender_profile.metrics.get(&block_number).unwrap();
        let recipient_metrics = recipient_profile.metrics.get(&block_number).unwrap();

        // Assuming metrics have spend_amount and receive_amount
        assert_eq!(sender_metrics.spend_amount, U256::from(100));
        assert_eq!(recipient_metrics.receive_amount, U256::from(100));

        // --- Check pending_deltas ---
        let block_deltas = evaluator.pending_deltas.get(&block_number).unwrap();
        assert!(block_deltas.contains_key(&sender));
        assert!(block_deltas.contains_key(&recipient));
    }

    #[test]
    fn test_update_profiles_batch_self_transfer_ignored() {
        let mut evaluator = new_evaluator();
        let addr = addr(1);

        let txs = vec![(addr, addr, U256::from(50))];
        let block_number = 10;

        evaluator.update_profiles_batch(&txs, block_number);

        // Should not insert self-transfer
        assert!(evaluator.latest_profiles.get(&addr).is_none());
        assert!(evaluator.pending_deltas.get(&block_number).unwrap().is_empty());
    }

    #[test]
    fn test_update_profiles_batch_multiple_txs_same_block() {
        let mut evaluator = new_evaluator();
        let a = addr(1);
        let b = addr(2);
        let c = addr(3);

        let txs = vec![
            (a, b, U256::from(10)),
            (b, c, U256::from(20)),
        ];
        let block_number = 5;

        evaluator.update_profiles_batch(&txs, block_number);

        // Check latest_profiles
        let a_profile = evaluator.latest_profiles.get(&a).unwrap();
        let b_profile = evaluator.latest_profiles.get(&b).unwrap();
        let c_profile = evaluator.latest_profiles.get(&c).unwrap();

        assert_eq!(a_profile.metrics.get(&block_number).unwrap().spend_amount, U256::from(10));
        assert_eq!(b_profile.metrics.get(&block_number).unwrap().spend_amount, U256::from(20));
        assert_eq!(b_profile.metrics.get(&block_number).unwrap().receive_amount, U256::from(10));
        assert_eq!(c_profile.metrics.get(&block_number).unwrap().receive_amount, U256::from(20));

        // Check pending_deltas
        let block_deltas = evaluator.pending_deltas.get(&block_number).unwrap();
        assert!(block_deltas.contains_key(&a));
        assert!(block_deltas.contains_key(&b));
        assert!(block_deltas.contains_key(&c));
    }

    // #[test]
    // fn test_basic_valid_transfer_updates_profiles() {
    //     let mut aml = new_evaluator();
    //     let sender = addr(1);
    //     let recipient = addr(2);
    //     let amount = U256::from(100);
    //     let block = 1;
    //
    //     // Check mempool transaction
    //     let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, block);
    //     assert!(ok, "Transfer should be allowed");
    //     assert!(reason.is_none(), "Transfer should pass AML checks");
    //
    //     // Verify mempool_profiles updated
    //     let sender_profile = aml.mempool_profiles.get(&sender).expect("Sender profile should exist");
    //     let recipient_profile = aml.mempool_profiles.get(&recipient).expect("Recipient profile should exist");
    //     assert_eq!(
    //         sender_profile.caches[0].sum, amount,
    //         "Sender daily_sum should match amount in mempool_profiles"
    //     );
    //     assert_eq!(
    //         recipient_profile.caches[0].inbound_sum, amount,
    //         "Recipient daily_sum should match amount in mempool_profiles"
    //     );
    //     assert_eq!(
    //         sender_profile.metrics.get(&block).unwrap().spend_amount, amount,
    //         "Sender spends should include amount in mempool_profiles"
    //     );
    //     assert_eq!(
    //         recipient_profile.metrics.get(&block).unwrap().receive_amount, amount,
    //         "Recipient spends should include amount in mempool_profiles"
    //     );
    //
    //     // Commit block with update_profiles_batch
    //     aml.update_profiles_batch(&[(sender, recipient, amount)], block);
    //
    //     // Verify mempool_profiles cleared and pending_profiles updated
    //     assert!(
    //         aml.mempool_profiles.is_empty(),
    //         "mempool_profiles should be cleared after update_profiles_batch"
    //     );
    //     let block_profiles = aml.pending_profiles.get(&block).expect("Block profiles should exist");
    //     let sender_profile = block_profiles.get(&sender).expect("Sender profile should exist");
    //     let recipient_profile = block_profiles.get(&recipient).expect("Recipient profile should exist");
    //
    //     assert_eq!(
    //         sender_profile.caches[0].sum, amount,
    //         "Sender daily_sum should match amount in pending_profiles"
    //     );
    //     assert_eq!(
    //         recipient_profile.caches[0].inbound_sum, amount,
    //         "Recipient daily_sum should match amount in pending_profiles"
    //     );
    //     assert_eq!(
    //         sender_profile.metrics.get(&block).unwrap().spend_amount, amount,
    //         "Sender spends should include amount in pending_profiles"
    //     );
    //     assert_eq!(
    //         recipient_profile.metrics.get(&block).unwrap().receive_amount, amount,
    //         "Recipient spends should include amount in pending_profiles"
    //     );
    //
    //     // Finalize block
    //     aml.update_finalized_block(block);
    //
    //     // Verify committed_profiles
    //     let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
    //     let recipient_profile = aml.committed_profiles.get(&recipient).expect("Recipient profile should exist");
    //
    //     assert_eq!(
    //         sender_profile.caches[0].sum, amount,
    //         "Committed sender daily_sum should match amount"
    //     );
    //     assert_eq!(
    //         recipient_profile.caches[0].inbound_sum, amount,
    //         "Committed recipient daily_sum should match amount"
    //     );
    // }

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

        println!("aml_pending profiles: {:?}", aml.mempool_profiles);

        // Verify sender's daily_sum
        let sender_profile = aml.mempool_profiles.get(&sender).expect("Sender profile should exist in mempool profiles");
        assert_eq!(
            sender_profile.caches[0].sum, amount,
            "Sender daily_sum should match first transaction"
        );
    }
    //
    // #[test]
    // fn benchmark_mempool_vs_batch() {
    //     let mut aml = new_evaluator();
    //     let sender = addr(1);
    //     let recipient = addr(2);
    //     let amount = U256::from(1);
    //     let num_txs = 10_000;
    //
    //     // Check mempool tx one by one
    //     let start = Instant::now();
    //     for i in 0..num_txs {
    //         let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);
    //         assert!(ok, "Tx {} should pass AML", i);
    //         assert!(reason.is_none());
    //     }
    //     let duration_mempool = start.elapsed();
    //     println!(
    //         "check_mempool_tx: validated {} txs in {:?} (avg {:?} per tx)",
    //         num_txs,
    //         duration_mempool,
    //         duration_mempool / num_txs as u32
    //     );
    //
    //     // Check compliance batch
    //     let txs: Vec<(Address, Address, U256)> =
    //         (0..num_txs).map(|_| (sender, recipient, amount)).collect();
    //     let start = Instant::now();
    //     let results = aml.check_compliance_batch(&txs, 1);
    //     let duration_batch = start.elapsed();
    //
    //     assert!(results.iter().all(|(ok, reason)| *ok && reason.is_none()));
    //     println!(
    //         "check_compliance_batch: validated {} txs in {:?} (avg {:?} per tx)",
    //         num_txs,
    //         duration_batch,
    //         duration_batch / num_txs as u32
    //     );
    //
    //     // Verify profile accounting
    //     aml.update_finalized_block(1);
    //     println!("{:?}", aml.committed_profiles);
    //     let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
    //     assert_eq!(
    //         sender_profile.daily_sum,
    //         U256::from(num_txs),
    //         "Sender daily_sum should match number of txs"
    //     );
    //     let recipient_profile = aml
    //         .committed_profiles
    //         .get(&recipient)
    //         .expect("Recipient profile should exist");
    //     assert_eq!(
    //         recipient_profile.daily_sum,
    //         U256::from(num_txs),
    //         "Recipient daily_sum should match number of txs"
    //     );
    // }
    //
    // #[test]
    // fn benchmark_profile_writes() {
    //     let mut aml = new_evaluator();
    //     let sender = addr(1);
    //     let recipient = addr(2);
    //     let amount = U256::from(1);
    //     let num_txs = 500;
    //
    //     // Prepare txs
    //     let txs: Vec<(Address, Address, U256)> =
    //         (0..num_txs).map(|_| (sender, recipient, amount)).collect();
    //
    //     // Benchmark write
    //     let start = Instant::now();
    //     aml.update_profiles_batch(&txs, 1);
    //     let elapsed = start.elapsed();
    //
    //     println!(
    //         "update_profiles_batch: {} txs in {:?} (avg {:?} per tx)",
    //         num_txs,
    //         elapsed,
    //         elapsed / num_txs as u32
    //     );
    //
    //     // Benchmark batch compliance only
    //     let start = Instant::now();
    //     let results = aml.check_compliance_batch(&txs, 1);
    //     let elapsed_batch = start.elapsed();
    //
    //     assert!(results.iter().all(|(ok, reason)| *ok && reason.is_none()));
    //     println!(
    //         "check_compliance_batch: {} txs in {:?} (avg {:?} per tx)",
    //         num_txs,
    //         elapsed_batch,
    //         elapsed_batch / num_txs as u32
    //     );
    //
    //     // Verify profile accounting
    //     aml.update_finalized_block(1);
    //     let sender_profile = aml.committed_profiles.get(&sender).expect("Sender profile should exist");
    //     assert_eq!(
    //         sender_profile.daily_sum,
    //         U256::from(num_txs),
    //         "Sender daily_sum should match number of txs"
    //     );
    //     let recipient_profile = aml
    //         .committed_profiles
    //         .get(&recipient)
    //         .expect("Recipient profile should exist");
    //     assert_eq!(
    //         recipient_profile.daily_sum,
    //         U256::from(num_txs),
    //         "Recipient daily_sum should match number of txs"
    //     );
    // }
}
