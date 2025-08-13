use std::collections::{HashMap, VecDeque};
use std::sync::{OnceLock, RwLock};
use alloy_primitives::{Address, U256};

const TIME_WINDOW_SECS: u64 = 7 * 24 * 60 * 60; // 7 days

const MAX_SINGLE_TX_AMOUNT: u128 = 10_000;
const MAX_TOTAL_SENT_7D: u128 = 100_000;
const MAX_TOTAL_RECEIVED_7D: u128 = 100_000;

pub static AML_EVALUATOR: OnceLock<RwLock<AmlEvaluator>> = OnceLock::new();

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    pub sent_amounts: VecDeque<(u128)>,
    pub recv_amounts: VecDeque<(u128)>,
    pub total_sent: u128,
    pub total_received: u128,
}

impl AccountProfile {
    pub fn new(address: Address) -> Self {
        Self {
            address,
            sent_amounts: VecDeque::new(),
            recv_amounts: VecDeque::new(),
            total_sent: 0,
            total_received: 0,
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
}

impl AmlEvaluator {
    pub fn new() -> Self {
        Self {
            profiles: HashMap::new(),
        }
    }

    fn check_compliance_internal(
        sender_profile: &AccountProfile,
        recipient_profile: &AccountProfile,
        amount: u128,
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
        amount: u128,
    ) {
        profile.total_sent += amount;
        profile.sent_amounts.push_back((amount));
    }

    fn update_recipient_profile(
        profile: &mut AccountProfile,
        amount: u128,
    ) {
        profile.total_received += amount;
        profile.recv_amounts.push_back(amount);
    }

    pub fn check_compliance_batch(
        &self,
        transactions: &[(Address, Address, U256)],
    ) -> Vec<(bool, Option<&'static str>)> {
        let mut temp_profiles = self.profiles.clone();
        let mut results = Vec::with_capacity(transactions.len());

        for &(sender, recipient, amount) in transactions {
            let amount_u128 = match amount.try_into() {
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


                let reason = Self::check_compliance_internal(profile, profile, amount_u128, true);

                if let Some(reason) = reason {
                    results.push((false, Some(reason)));
                } else {
                    Self::update_sender_profile(profile, amount_u128);
                    Self::update_recipient_profile(profile, amount_u128);
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

                let reason = Self::check_compliance_internal(
                    &sender_profile,
                    &recipient_profile,
                    amount_u128,
                    false,
                );

                if let Some(reason) = reason {
                    results.push((false, Some(reason)));
                } else {
                    Self::update_sender_profile(&mut sender_profile, amount_u128);
                    Self::update_recipient_profile(&mut recipient_profile, amount_u128);
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
        let amount_u128 = match amount.try_into() {
            Ok(v) => v,
            Err(_) => return,
        };

        if sender == recipient {
            let profile = self
                .profiles
                .entry(sender)
                .or_insert_with(|| AccountProfile::new(sender));

            Self::update_sender_profile(profile, amount_u128);
            Self::update_recipient_profile(profile, amount_u128);
        } else {
            {
                let sender_profile = self
                    .profiles
                    .entry(sender)
                    .or_insert_with(|| AccountProfile::new(sender));
                Self::update_sender_profile(sender_profile, amount_u128);
            }

            {
                let recipient_profile = self
                    .profiles
                    .entry(recipient)
                    .or_insert_with(|| AccountProfile::new(recipient));
                Self::update_recipient_profile(recipient_profile, amount_u128);
            }
        }
    }
}
