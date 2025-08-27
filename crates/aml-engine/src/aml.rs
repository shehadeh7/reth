use std::collections::{HashMap, VecDeque};
use std::sync::{OnceLock, RwLock};
use alloy_primitives::{Address, U256};

const TIME_WINDOW_SECS: u64 = 7 * 24 * 60 * 60; // 7 days

// 100 * 1e18 = 100000000000000000000
pub const MAX_SINGLE_TX_AMOUNT: U256 = U256::from_limbs([
    0x6BC75E2D63100000, // Limb 0 (LSB)
    0x5, // Limb 1
    0x0,                 // Limb 2
    0x0,                 // Limb 3 (MSB)
]);

// 1_000 * 1e18 = 1000000000000000000000
pub const MAX_TOTAL_SENT_7D: U256 = U256::from_limbs([
    0x35C9ADC5DEA00000,
    0x36,
    0x0,
    0x0,
]);

// 10_000 * 1e18 = 10000000000000000000000
pub const MAX_TOTAL_RECEIVED_7D: U256 = U256::from_limbs([
    0x19E0C9BAB2400000,
    0x21E,
    0x0,
    0x0,
]);

pub static AML_EVALUATOR: OnceLock<RwLock<AmlEvaluator>> = OnceLock::new();

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    pub sent_amounts: VecDeque<(u64, U256)>,
    pub recv_amounts: VecDeque<(u64, U256)>,
    pub total_sent: U256,
    pub total_received: U256,
}

impl AccountProfile {
    pub fn new(address: Address) -> Self {
        Self {
            address,
            sent_amounts: VecDeque::new(),
            recv_amounts: VecDeque::new(),
            total_sent: U256::from(0),
            total_received: U256::from(0),
        }
    }

    pub fn prune_old(&mut self, now: u64) {
        while let Some(&(ts, amt)) = self.sent_amounts.front() {
            if now.saturating_sub(ts) > TIME_WINDOW_SECS {
                self.sent_amounts.pop_front();
                self.total_sent = self.total_sent.saturating_sub(amt);
            } else {
                break;
            }
        }

        while let Some(&(ts, amt)) = self.recv_amounts.front() {
            if now.saturating_sub(ts) > TIME_WINDOW_SECS {
                self.recv_amounts.pop_front();
                self.total_received = self.total_received.saturating_sub(amt);
            } else {
                break;
            }
        }
    }
}

#[derive(Debug)]
pub struct AmlEvaluator {
    profiles: HashMap<Address, AccountProfile>,
    pending_profiles: HashMap<Address, AccountProfile>,
}

impl AmlEvaluator {
    pub fn new() -> Self {
        Self {
            profiles: HashMap::new(),
            pending_profiles: HashMap::new(),
        }
    }

    fn check_compliance_internal(
        sender_profile: &AccountProfile,
        recipient_profile: &AccountProfile,
        amount: U256,
    ) -> Option<&'static str> {
        if amount > MAX_SINGLE_TX_AMOUNT {
            return Some("single_transaction_above_threshold");
        }

        if sender_profile.total_sent + amount > MAX_TOTAL_SENT_7D {
            return Some("total_sent_7d_threshold_exceeded");
        }

        if recipient_profile.total_received + amount > MAX_TOTAL_RECEIVED_7D {
            return Some("total_received_7d_threshold_exceeded");
        }

        None
    }


    fn update_sender_profile(profile: &mut AccountProfile, block_number: u64, amount: U256) {
        profile.total_sent += amount;
        profile.sent_amounts.push_back((block_number, amount));
    }

    fn update_recipient_profile(profile: &mut AccountProfile, block_number: u64, amount: U256) {
        profile.total_received += amount;
        profile.recv_amounts.push_back((block_number, amount));
    }

    pub fn check_mempool_tx(
        &mut self,
        sender: Address,
        recipient: Address,
        amount: U256,
        block_number: u64,
    ) -> (bool, Option<&'static str>) {
        if self.pending_profiles.is_empty() {
            self.pending_profiles = self.profiles.clone();
        }

        let amount = match amount.try_into() {
            Ok(v) => v,
            Err(_) => return (false, Some("amount_conversion_failed")),
        };

        if sender == recipient {
            return (true, None) // no-op
        }

        let mut sender_profile = self.pending_profiles
            .remove(&sender)
            .unwrap_or_else(|| AccountProfile::new(sender));
        let mut recipient_profile = self.pending_profiles
            .remove(&recipient)
            .unwrap_or_else(|| AccountProfile::new(recipient));

        let reason = Self::check_compliance_internal(
            &sender_profile,
            &recipient_profile,
            amount,
        );

        if let Some(reason) = reason {
            // Don't update profiles, just reinsert the originals
            self.pending_profiles.insert(sender, sender_profile);
            self.pending_profiles.insert(recipient, recipient_profile);
            (false, Some(reason))
        } else {
            Self::update_sender_profile(&mut sender_profile, block_number, amount);
            Self::update_recipient_profile(&mut recipient_profile, block_number, amount);
            self.pending_profiles.insert(sender, sender_profile);
            self.pending_profiles.insert(recipient, recipient_profile);
            (true, None)
        }
    }

    /// Method to revert a single pending transaction from pending profiles
    pub fn revert_mempool_tx(&mut self, sender: Address, recipient: Address, amount: U256) {
        if sender == recipient {
            return; // no-op
        } else {
            if let Some(sender_profile) = self.pending_profiles.get_mut(&sender) {
                sender_profile.total_sent = sender_profile.total_sent.saturating_sub(amount);
            }
            if let Some(recipient_profile) = self.pending_profiles.get_mut(&recipient) {
                recipient_profile.total_received = recipient_profile.total_received.saturating_sub(amount);
            }
        }
    }

    pub fn check_compliance_batch(
        &self,
        transactions: &[(Address, Address, U256)],
        block_number: u64,
    ) -> Vec<(bool, Option<&'static str>)> {
        let mut temp_profiles = self.profiles.clone();
        let mut results = Vec::with_capacity(transactions.len());

        for &(sender, recipient, amount) in transactions {
            let amount = match amount.try_into() {
                Ok(v) => v,
                Err(_) => {
                    results.push((false, Some("amount_conversion_failed")));
                    continue;
                }
            };

            if sender == recipient {
                results.push((true, None));
            } else {
                // Get sender and recipient profiles separately to avoid mutable borrow conflict
                let mut sender_profile = temp_profiles
                    .remove(&sender)
                    .unwrap_or_else(|| AccountProfile::new(sender));
                let mut recipient_profile = temp_profiles
                    .remove(&recipient)
                    .unwrap_or_else(|| AccountProfile::new(recipient));

                // println!("sender_profile: {:?}, recipient_profile: {:?}", sender_profile, recipient_profile);

                let reason = Self::check_compliance_internal(
                    &sender_profile,
                    &recipient_profile,
                    amount,
                );

                if let Some(reason) = reason {
                    results.push((false, Some(reason)));
                } else {
                    Self::update_sender_profile(&mut sender_profile, block_number, amount);
                    Self::update_recipient_profile(&mut recipient_profile, block_number, amount);
                    results.push((true, None));
                }

                // Reinsert into map
                temp_profiles.insert(sender, sender_profile);
                temp_profiles.insert(recipient, recipient_profile);
            }
        }

        results
    }

    pub fn update_profiles(&mut self, sender: Address, recipient: Address, amount: U256, block_number: u64) {
        if sender == recipient { return; }

        { let sender_profile = self.profiles.entry(sender).or_insert_with(|| AccountProfile::new(sender)); sender_profile.prune_old(block_number); Self::update_sender_profile(sender_profile, block_number, amount); }

        { let recipient_profile = self.profiles.entry(recipient).or_insert_with(|| AccountProfile::new(recipient)); recipient_profile.prune_old(block_number); Self::update_recipient_profile(recipient_profile, block_number, amount); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};
    use std::time::Instant;

    fn addr(byte: u8) -> Address {
        // helper to make dummy addresses like 0x000..01, 0x000..02, etc.
        Address::repeat_byte(byte)
    }

    #[test]
    fn test_self_transfer_is_noop() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let amount = U256::from(1000);

        let (ok, reason) = aml.check_mempool_tx(sender, sender, amount, 1);
        assert!(ok, "Self-transfer should be allowed");
        assert!(reason.is_none(), "Self-transfer should not trigger AML checks");

        // Profiles should not be updated
        assert!(aml.pending_profiles.get(&sender).is_none());
        assert!(aml.profiles.get(&sender).is_none());
    }

    #[test]
    fn test_basic_valid_transfer_updates_profiles() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(100);

        let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);
        assert!(ok, "Transfer should be allowed");
        assert!(reason.is_none());

        // Commit the profiles
        aml.update_profiles(sender, recipient, amount, 1);

        let sender_profile = aml.profiles.get(&sender).unwrap();
        let recipient_profile = aml.profiles.get(&recipient).unwrap();

        assert_eq!(sender_profile.total_sent, amount);
        assert_eq!(recipient_profile.total_received, amount);
    }

    #[test]
    fn test_single_tx_threshold_rejected() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let recipient = addr(2);

        // Amount bigger than MAX_SINGLE_TX_AMOUNT should be rejected
        let big_amount = MAX_SINGLE_TX_AMOUNT + U256::from(1);

        let (ok, reason) = aml.check_mempool_tx(sender, recipient, big_amount, 1);
        assert!(!ok, "Transfer above threshold should be rejected");
        assert_eq!(reason, Some("single_transaction_above_threshold"));
    }

    #[test]
    fn test_total_sent_7d_threshold_rejected() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let recipient = addr(2);

        // Push sender near the limit
        {
            let sender_profile = aml.profiles.entry(sender).or_insert_with(|| AccountProfile::new(sender));
            sender_profile.total_sent = MAX_TOTAL_SENT_7D;
        }

        let amount = U256::from(1);
        let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, 1);

        assert!(!ok, "Transfer above 7d sent limit should be rejected");
        assert_eq!(reason, Some("total_sent_7d_threshold_exceeded"));
    }

    #[test]
    fn test_batch_compliance_mixed_results() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let recipient = addr(2);

        // Batch with one valid tx and one failing tx
        let txs = vec![
            (sender, recipient, U256::from(10)),                // valid
            (sender, recipient, MAX_SINGLE_TX_AMOUNT + U256::from(1)) // invalid
        ];

        let results = aml.check_compliance_batch(&txs, 1);
        assert_eq!(results.len(), 2);

        assert_eq!(results[0], (true, None));
        assert_eq!(results[1], (false, Some("single_transaction_above_threshold")));
    }

    #[test]
    fn benchmark_mempool_vs_batch() {
        let mut aml = AmlEvaluator::new();
        let sender = addr(1);
        let recipient = addr(2);
        let amount = U256::from(1);

        let num_txs = 3000;

        // --------- Check mempool tx one by one ---------
        let start = Instant::now();
        for i in 0..num_txs {
            let (ok, reason) = aml.check_mempool_tx(sender, recipient, amount, i);
            assert!(ok, "tx {} should pass AML", i);
            assert!(reason.is_none());
        }
        let duration_mempool = start.elapsed();
        println!(
            "check_mempool_tx: validated {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            duration_mempool,
            duration_mempool / num_txs as u32
        );

        // --------- Check compliance batch ---------
        let txs: Vec<(Address, Address, U256)> =
            (0..num_txs).map(|_| (sender, recipient, amount)).collect();

        let start = Instant::now();
        let results = aml.check_compliance_batch(&txs, 1);
        let duration_batch = start.elapsed();

        // validate all passed
        assert!(results.iter().all(|(ok, reason)| *ok && reason.is_none()));

        println!(
            "check_compliance_batch: validated {} txs in {:?} (avg {:?} per tx)",
            num_txs,
            duration_batch,
            duration_batch / num_txs as u32
        );

        // --------- Verify profile accounting ---------
        aml.update_profiles(sender, recipient, U256::from(num_txs), 1);

        let sender_profile = aml.profiles.get(&sender).unwrap();
        let recipient_profile = aml.profiles.get(&recipient).unwrap();

        assert_eq!(
            sender_profile.total_sent,
            U256::from(num_txs),
            "sender total_sent should match number of txs"
        );
        assert_eq!(
            recipient_profile.total_received,
            U256::from(num_txs),
            "recipient total_received should match number of txs"
        );
    }
}
