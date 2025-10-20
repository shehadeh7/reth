use alloy_primitives::{Address, U256};
use crate::account_profile::WindowCache;

pub trait AmlRule: std::fmt::Debug + Send + Sync + 'static {
    fn name(&self) -> &'static str;

    /// Stateless evaluation: reads caches, does not mutate anything.
    fn would_exceed(
        &self,
        caches: &[WindowCache],
        new_amount: U256,
        new_recipient: Address,
        new_sender: Address,
        is_sender: bool,
    ) -> bool;
}

// Example 1: Outbound sum limit rule
#[derive(Debug)]
pub struct OutboundSumRule {
    pub limit_per_window: Vec<U256>, // One limit per window duration
}

impl AmlRule for OutboundSumRule {
    fn name(&self) -> &'static str {
        "OutboundSumRule"
    }

    fn would_exceed(
        &self,
        caches: &[WindowCache],
        new_amount: U256,
        _recipient: Address,
        _sender: Address,
        is_sender: bool,
    ) -> bool {
        if !is_sender {
            return false;
        }

        caches.iter()
            .zip(self.limit_per_window.iter())
            .any(|(cache, &limit)| cache.sum + new_amount > limit)
    }
}

#[derive(Debug)]
pub struct OutboundCountRule {
    pub count_limits: Vec<u32>, // One per window
}

impl AmlRule for OutboundCountRule {
    fn name(&self) -> &'static str { "OutboundCountRule" }

    fn would_exceed(
        &self,
        caches: &[WindowCache],
        _new_amount: U256,
        _recipient: Address,
        _sender: Address,
        is_sender: bool,
    ) -> bool {
        if !is_sender { return false; }

        caches.iter()
            .zip(self.count_limits.iter())
            .any(|(cache, &limit)| cache.count + 1 > limit)
    }
}

#[derive(Debug)]
pub struct InboundSumRule {
    pub inbound_sum_limits: Vec<U256>, // One per window
}

impl AmlRule for InboundSumRule {
    fn name(&self) -> &'static str { "InboundSumRule" }

    fn would_exceed(
        &self,
        caches: &[WindowCache],
        new_amount: U256,
        _recipient: Address,
        _sender: Address,
        is_sender: bool,
    ) -> bool {
        if is_sender { return false; }

        caches.iter()
            .zip(self.inbound_sum_limits.iter())
            .any(|(cache, &limit)| cache.inbound_sum + new_amount > limit)
    }
}
