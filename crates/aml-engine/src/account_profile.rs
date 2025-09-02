use std::collections::VecDeque;
use alloy_primitives::{Address, U256};

const TIME_WINDOW_SECS: u64 = 7 * 24 * 60 * 60; // 7 days

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
