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
    pub sent_amounts: VecDeque<(U256)>,
    pub recv_amounts: VecDeque<(U256)>,
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

    // pub fn prune_old(&mut self, now: u64) {
    //     while let Some(&(ts, amt)) = self.sent_amounts.front() {
    //         if now.saturating_sub(ts) > TIME_WINDOW_SECS {
    //             self.sent_amounts.pop_front();
    //             self.total_sent = self.total_sent.saturating_sub(amt);
    //         } else {
    //             break;
    //         }
    //     }
    //
    //     while let Some(&(ts, amt)) = self.recv_amounts.front() {
    //         if now.saturating_sub(ts) > TIME_WINDOW_SECS {
    //             self.recv_amounts.pop_front();
    //             self.total_received = self.total_received.saturating_sub(amt);
    //         } else {
    //             break;
    //         }
    //     }
    // }
}

#[derive(Debug, Clone)]
pub struct AmlEvaluator {
    pub profiles: HashMap<Address, AccountProfile>,
    pub pending_profiles: HashMap<Address, AccountProfile>,
    pub last_seen_block_timestamp: u64,
}

impl AmlEvaluator {
    pub fn new() -> Self {
        Self {
            profiles: HashMap::new(),
            pending_profiles: HashMap::new(),
            last_seen_block_timestamp: 0, // store latest when updating , figure out initialization later
        }
    }

    fn check_compliance_internal(
        sender_profile: &AccountProfile,
        recipient_profile: &AccountProfile,
        amount: U256,
        sender_eq_recipient: bool,
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

        if sender_eq_recipient {
            if sender_profile.total_received + amount > MAX_TOTAL_RECEIVED_7D {
                return Some("total_received_7d_threshold_exceeded");
            }
        }

        None
    }

    fn update_sender_profile(
        profile: &mut AccountProfile,
        amount: U256,
    ) {
        profile.total_sent += amount;
        profile.sent_amounts.push_back((amount));
    }

    fn update_recipient_profile(
        profile: &mut AccountProfile,
        amount: U256,
    ) {
        profile.total_received += amount;
        profile.recv_amounts.push_back(amount);
    }

    pub fn check_mempool_tx(
        &mut self,
        sender: Address,
        recipient: Address,
        amount: U256,
    ) -> (bool, Option<&'static str>) {
        if self.pending_profiles.is_empty() {
            self.pending_profiles = self.profiles.clone();
        }

        let amount = match amount.try_into() {
            Ok(v) => v,
            Err(_) => return (false, Some("amount_conversion_failed")),
        };

        if sender == recipient {
            let profile = self.pending_profiles
                .entry(sender)
                .or_insert_with(|| AccountProfile::new(sender));

            let reason = Self::check_compliance_internal(profile, profile, amount, true);

            if let Some(reason) = reason {
                (false, Some(reason))
            } else {
                Self::update_sender_profile(profile, amount);
                Self::update_recipient_profile(profile, amount);
                (true, None)
            }
        } else {
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
                false,
            );

            if let Some(reason) = reason {
                // Don't update profiles, just reinsert the originals
                self.pending_profiles.insert(sender, sender_profile);
                self.pending_profiles.insert(recipient, recipient_profile);
                (false, Some(reason))
            } else {
                Self::update_sender_profile(&mut sender_profile, amount);
                Self::update_recipient_profile(&mut recipient_profile, amount);
                self.pending_profiles.insert(sender, sender_profile);
                self.pending_profiles.insert(recipient, recipient_profile);
                (true, None)
            }
        }
    }

    /// Method to revert a single pending transaction from pending profiles
    pub fn revert_mempool_tx(&mut self, sender: Address, recipient: Address, amount: U256) {
        if sender == recipient {
            if let Some(profile) = self.pending_profiles.get_mut(&sender) {
                profile.total_sent = profile.total_sent.saturating_sub(amount);
                profile.total_received = profile.total_received.saturating_sub(amount);
            }
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
                let profile = temp_profiles
                    .entry(sender)
                    .or_insert_with(|| AccountProfile::new(sender));


                let reason = Self::check_compliance_internal(profile, profile, amount, true);

                if let Some(reason) = reason {
                    results.push((false, Some(reason)));
                } else {
                    Self::update_sender_profile(profile, amount);
                    Self::update_recipient_profile(profile, amount);
                    results.push((true, None));
                }
            } else {
                // Get sender and recipient profiles separately to avoid mutable borrow conflict
                let mut sender_profile = temp_profiles
                    .remove(&sender)
                    .unwrap_or_else(|| AccountProfile::new(sender));
                let mut recipient_profile = temp_profiles
                    .remove(&recipient)
                    .unwrap_or_else(|| AccountProfile::new(recipient));

                println!("sender_profile: {:?}, recipient_profile: {:?}", sender_profile, recipient_profile);

                let reason = Self::check_compliance_internal(
                    &sender_profile,
                    &recipient_profile,
                    amount,
                    false,
                );

                if let Some(reason) = reason {
                    results.push((false, Some(reason)));
                } else {
                    Self::update_sender_profile(&mut sender_profile, amount);
                    Self::update_recipient_profile(&mut recipient_profile, amount);
                    results.push((true, None));
                }

                // Reinsert into map
                temp_profiles.insert(sender, sender_profile);
                temp_profiles.insert(recipient, recipient_profile);
            }
        }

        results
    }

    pub fn update_profiles(
        &mut self,
        sender: Address,
        recipient: Address,
        amount: U256,
    ) {
        if sender == recipient {
            let profile = self
                .profiles
                .entry(sender)
                .or_insert_with(|| AccountProfile::new(sender));

            Self::update_sender_profile(profile, amount);
            Self::update_recipient_profile(profile, amount);
        } else {
            {
                let sender_profile = self
                    .profiles
                    .entry(sender)
                    .or_insert_with(|| AccountProfile::new(sender));
                Self::update_sender_profile(sender_profile, amount);
            }

            {
                let recipient_profile = self
                    .profiles
                    .entry(recipient)
                    .or_insert_with(|| AccountProfile::new(recipient));
                Self::update_recipient_profile(recipient_profile, amount);
            }
        }
    }
}
