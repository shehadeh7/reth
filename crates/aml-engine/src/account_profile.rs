use std::collections::{HashMap, VecDeque};
use alloy_primitives::{Address, U256};

#[derive(Debug, Clone)]
pub struct AccountProfile {
    pub address: Address,
    pub sent_amounts: VecDeque<(u64, U256, Address)>,
    pub recv_amounts: VecDeque<(u64, U256, Address)>,
    pub total_sent: U256,
    pub total_received: U256,

    // Mule-specific features
    pub unique_senders: HashMap<Address, u64>,     // senders in current window
    pub unique_recipients: HashMap<Address, u64>,  // recipients in current window
    pub first_seen_block: u64,                // for lifetime analysis
}

impl AccountProfile {
    pub fn new(address: Address, block_number: u64) -> Self {
        Self {
            address,
            sent_amounts: VecDeque::new(),
            recv_amounts: VecDeque::new(),
            total_sent: U256::from(0),
            total_received: U256::from(0),
            unique_senders: HashMap::new(),
            unique_recipients: HashMap::new(),
            first_seen_block: block_number,
        }
    }

    pub fn prune_old(&mut self, now: u64, window: u64) {
        // Prune sent amounts
        while let Some(front) = self.sent_amounts.front().cloned() {
            let (block, amt, recipient) = front;
            if now.saturating_sub(block) > window {
                self.sent_amounts.pop_front();
                self.total_sent = self.total_sent.saturating_sub(amt);

                if let Some(&last_seen) = self.unique_recipients.get(&recipient) {
                    if last_seen == block {
                        self.unique_recipients.remove(&recipient);
                    }
                }
            } else {
                break;
            }
        }

        // Prune received amounts
        while let Some(front) = self.recv_amounts.front().cloned() {
            let (block, amt, sender) = front;
            if now.saturating_sub(block) > window {
                self.recv_amounts.pop_front();
                self.total_received = self.total_received.saturating_sub(amt);

                if let Some(&last_seen) = self.unique_senders.get(&sender) {
                    if last_seen == block {
                        self.unique_senders.remove(&sender);
                    }
                }
            } else {
                break;
            }
        }
    }
}
