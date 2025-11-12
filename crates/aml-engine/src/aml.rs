use crate::account_profile::{AccountProfile};
use alloy_primitives::{keccak256, Address, FixedBytes, B256, U256};
use std::collections::{HashMap};
use std::num::NonZeroUsize;
use std::sync::{OnceLock, RwLock};
use lru::LruCache;
use revm_primitives::KECCAK_EMPTY;
use reth_provider::StateProvider;
use crate::aml_db::{AccountProfileDb, AmlDb};
use crate::aml_graph::{AMLMotifDetector, Config};
use crate::aml_rules::{AmlRule, InboundSumRule, OutboundCountRule, OutboundSumRule};

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
    pub aml_support_cache: HashMap<Address, bool>, // Token addresses for AML
    motif_detector: AMLMotifDetector,
}

impl AmlEvaluator {
    pub fn new() -> Self {
        let motif_config: Config =  Config {
            window_blocks: 7200,
            fan_in_count_threshold: 100,
            fan_in_sum_threshold: DAILY_LIMIT.saturating_add(DAILY_LIMIT),
            scatter_gather_threshold: DAILY_LIMIT.saturating_mul(U256::from(3)),
            gather_scatter_threshold: DAILY_LIMIT.saturating_mul(U256::from(3)),
            enable_peel_chain_detection: true,
        };

        Self {
            aml_support_cache: HashMap::new(),
            motif_detector: AMLMotifDetector::new(motif_config),
        }
    }

    pub fn check_mempool_tx(
        &mut self,
        token: Address,
        sender: Address,
        recipient: Address,
        amount: U256,
        block_number: u64,
        parent_hash: B256,
    ) -> (bool, Option<&'static str>) {
        if sender == recipient {
            return (true, None); // no-op
        }

        // Ignore string return for now
        (self.motif_detector.proposer_check_tx(sender, recipient, amount, block_number, parent_hash), Option::None)
    }

    pub fn check_compliance_batch(
        &mut self,
        transactions: &[(Address, Address, Address, U256)],
        block_number: u64,
        parent_hash: B256,
    ) -> bool {
        let filtered: Vec<(Address, Address, U256)> =
            transactions.iter().map(|&(_, a, b, v)| (a, b, v)).collect();
        self.motif_detector.consensus_validate_block(&filtered, block_number, parent_hash)
    }

    pub fn update_profiles_batch(
        &mut self,
        block: u64,
        parent_hash: B256,
        all_txs: &[(Address, Address, U256)],
        successful_indices: &[usize],
    ) {
        if all_txs.is_empty() {
            return;
        }

        self.motif_detector.block_commit(block, parent_hash, all_txs, successful_indices);
    }

    /// Reorg/fork handling
    pub fn handle_reorg(
        &mut self,
        old_blocks: &[u64],
        new_blocks: &[(u64, B256, Vec<(Address, Address, U256)>, Vec<usize>)],
    ) {
        // Step 1: Revert motif detector
        self.motif_detector.reorg_revert(old_blocks);

        // Step 2: Apply new canonical blocks
        for (block_number, parent_hash, all_txs, successful_indices) in new_blocks {
            self.motif_detector.block_commit(
                *block_number,
                *parent_hash,
                all_txs,
                successful_indices,
            );
        }
    }

    /// Checks if the token address is onboarded to AML check
    pub fn supports_aml_interface<S: StateProvider>(
        &mut self,
        contract_address: Address,
        state: &S,
    ) -> bool {
        // Check cache first
        if let Some(&supported) = self.aml_support_cache.get(&contract_address) {
            return supported;
        }

        // Calculate selector for supportsAML()
        let selector = FixedBytes::<4>::from_slice(&keccak256("supportsAML()")[..4]);

        // Get contract account
        let account = match state.basic_account(&contract_address) {
            Ok(Some(acc)) => acc,
            _ => {
                self.aml_support_cache.insert(contract_address, false);
                return false;
            }
        };

        // Check if contract exists
        if account.bytecode_hash == Some(KECCAK_EMPTY) {
            self.aml_support_cache.insert(contract_address, false);
            return false;
        }

        // Get the bytecode
        let code = match state.bytecode_by_hash(&account.bytecode_hash.unwrap()) {
            Ok(Some(code)) => code,
            _ => {
                self.aml_support_cache.insert(contract_address, false);
                return false;
            }
        };

        let bytecode = code.bytecode().as_ref();

        // Look for complete dispatcher pattern: PUSH4 <selector> EQ JUMPI
        // PUSH4 = 0x63, EQ = 0x14, JUMPI = 0x57
        let supports_aml = bytecode.windows(7).any(|window| {
            window[0] == 0x63 &&                      // PUSH4
                &window[1..5] == selector.as_slice()  // selector bytes
        });

        // Cache the result
        self.aml_support_cache.insert(contract_address, supports_aml);

        supports_aml
    }
}
