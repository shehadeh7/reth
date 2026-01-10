use crate::account_profile::{AccountProfile};
use alloy_primitives::{keccak256, Address, FixedBytes, B256, U256};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::OpenOptions;
use std::io::Write;
use std::num::NonZeroUsize;
use std::str::FromStr;
use std::sync::{Mutex, OnceLock, RwLock};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use lru::LruCache;
use revm_primitives::KECCAK_EMPTY;
use reth_provider::StateProvider;
use crate::aml_db::{AccountProfileDb, AmlDb};
use crate::aml_graph::{AMLMotifDetector, Config};
use crate::aml_rules::{AmlRule, InboundSumRule, OutboundCountRule, OutboundSumRule};
use chrono::Local;


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

lazy_static::lazy_static! {
    static ref RUN_TIMESTAMP: String = {
        let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
        let path = format!("experiment_logs/{}", timestamp);
        fs::create_dir_all(&path).expect("Failed to create run directory");
        timestamp
    };

    static ref MEMPOOL_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs/{}/mempool_latency.csv", *RUN_TIMESTAMP))
            .expect("Failed to open mempool_latency.csv");
        writeln!(file, "unix_timestamp,block_number,latency_micros,passed")
            .expect("Failed to write header");
        file
    });

    static ref BLOCK_COMMIT_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs/{}/block_commit_latency.csv", *RUN_TIMESTAMP))
            .expect("Failed to open block_commit_latency.csv");
        writeln!(file, "unix_timestamp,block_number,num_txs,latency_micros")
            .expect("Failed to write header");
        file
    });

    static ref CONSENSUS_VALIDATE_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs/{}/consensus_validate_latency.csv", *RUN_TIMESTAMP))
            .expect("Failed to open consensus_validate_latency.csv");
        writeln!(file, "unix_timestamp,block_number,num_txs,latency_micros")
            .expect("Failed to write header");
        file
    });

    static ref MEMORY_LOG: Mutex<std::fs::File> = Mutex::new({
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("experiment_logs/{}/memory_measurement.csv", *RUN_TIMESTAMP))
            .expect("Failed to open memory_measurement.csv");
        writeln!(file, "unix_timestamp,block_number,memory_bytes")
            .expect("Failed to write header");
        file
    });
}

fn get_unix_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

pub fn log_mempool_check(
    block_number: u64,
    tx_hash: B256,
    sender: Address,
    recipient: Address,
    amount: U256,
    latency_micros: u128,
    passed: bool,
) {
    if let Ok(mut file) = MEMPOOL_LOG.lock() {
        writeln!(
            file,
            "{},{},{},{}",
            get_unix_timestamp(),
            block_number,
            latency_micros,
            passed
        ).ok();
    }
}

pub fn log_block_commit(
    block_number: u64,
    num_txs: usize,
    latency_micros: u128,
) {
    if let Ok(mut file) = BLOCK_COMMIT_LOG.lock() {
        writeln!(
            file,
            "{},{},{},{}",
            get_unix_timestamp(),
            block_number,
            num_txs,
            latency_micros
        ).ok();
    }
}

pub fn log_consensus_validate(
    block_number: u64,
    num_txs: usize,
    latency_micros: u128,
) {
    if let Ok(mut file) = CONSENSUS_VALIDATE_LOG.lock() {
        writeln!(
            file,
            "{},{},{},{}",
            get_unix_timestamp(),
            block_number,
            num_txs,
            latency_micros
        ).ok();
    }
}

pub fn log_memory_usage(
    block_number: u64,
    memory_bytes: usize,
) {
    if let Ok(mut file) = MEMORY_LOG.lock() {
        writeln!(
            file,
            "{},{},{}",
            get_unix_timestamp(),
            block_number,
            memory_bytes
        ).ok();
    }
}


pub static AML_EVALUATOR: OnceLock<RwLock<AmlEvaluator>> = OnceLock::new();

pub struct AmlEvaluator {
    pub aml_support_cache: HashMap<Address, bool>, // Token addresses for AML
    motif_detector: AMLMotifDetector,
    pub block_number: u64,
}

impl AmlEvaluator {
    pub fn new() -> Self {
        let motif_config: Config = Config {
            window_blocks: 1,
            fan_in_count_threshold: 100000000000,
            fan_in_sum_threshold: U256::from_str("100000000000000000000000000000000").unwrap(),
            scatter_gather_threshold: U256::from_str("100000000000000000000000000000000").unwrap(),
            gather_scatter_threshold: U256::from_str("100000000000000000000000000000000").unwrap(),
            fan_out_count_threshold: 100000000000,
            fan_out_sum_threshold: U256::from_str("100000000000000000000000000000000").unwrap(),
        };

        Self {
            aml_support_cache: HashMap::new(),
            motif_detector: AMLMotifDetector::new(motif_config),
            block_number: 0,
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
            return (false, None); // no-op
        }

        // Ignore string return for now
        (self.motif_detector.proposer_check_tx(sender, recipient, amount, token, block_number, parent_hash), Option::None)
    }

    pub fn check_compliance_batch(
        &mut self,
        transactions: &[(Address, Address, Address, U256)],
        block_number: u64,
        parent_hash: B256,
    ) -> Vec<usize> {
        if transactions.is_empty() {
            return Vec::new();
        }
        // let filtered: Vec<(Address, Address, U256)> =
        //     transactions.iter().map(|&(_, a, b, v)| (a, b, v)).collect();
        self.motif_detector.consensus_validate_block(&transactions, block_number, parent_hash)
    }

    pub fn update_profiles_batch(
        &mut self,
        block: u64,
        parent_hash: B256,
        successful_txs: &[(Address, Address, Address, U256)]
    ) {
        // println!("successful_txs {:?}", successful_txs.len());
        self.motif_detector.block_commit(block, parent_hash, successful_txs);
    }

    /// Reorg/fork handling
    pub fn handle_reorg(
        &mut self,
        old_blocks: &[u64],
        new_blocks: &[(u64, B256, Vec<(Address, Address, Address, U256)>)],
    ) {
        let old_set: HashSet<u64> = old_blocks.iter().copied().collect();
        let new_blocks_map: HashMap<u64, &(u64, B256, Vec<(Address, Address, Address, U256)>)> =
            new_blocks.iter().map(|b| (b.0, b)).collect();
        let new_set: HashSet<u64> = new_blocks_map.keys().copied().collect();

        // Determine window boundary
        let current_tip = self.motif_detector.block_queue.back().copied();
        let window_start = current_tip
            .map(|tip| tip.saturating_sub(self.motif_detector.config.window_blocks))
            .unwrap_or(0);

        // Categorize blocks
        let blocks_in_both: Vec<u64> = old_set.intersection(&new_set)
            .filter(|&&b| b >= window_start)
            .copied()
            .collect();

        let blocks_only_in_old: Vec<u64> = old_set.difference(&new_set)
            .filter(|&&b| b >= window_start)
            .copied()
            .collect();

        let blocks_only_in_new: Vec<u64> = new_set.difference(&old_set)
            .filter(|&&b| b >= window_start)
            .copied()
            .collect();

        // Execute reorg
        self.motif_detector.execute_reorg(
            &blocks_in_both,
            &blocks_only_in_old,
            &blocks_only_in_new,
            &new_blocks_map,
        );
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
                return false;
            }
        };

        // Check if contract exists
        if account.bytecode_hash == Some(KECCAK_EMPTY) {
            return false;
        }

        // Get the bytecode
        let code = match state.bytecode_by_hash(&account.bytecode_hash.unwrap()) {
            Ok(Some(code)) => code,
            _ => {
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

    pub fn measure_memory_overhead(&self, block: u64) {
        let graph_overhead = self.motif_detector.estimate_internal_memory();
        log_memory_usage(block, graph_overhead);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_reorg_all_cases() {
        // Setup: Create motif detector with initial state
        let mut detector = AmlEvaluator::new();

        // Initial state: Add blocks 100, 101, 102, 103 to the graph
        let addr1 = Address::from([1u8; 20]);
        let addr2 = Address::from([2u8; 20]);
        let addr3 = Address::from([3u8; 20]);
        let addr4 = Address::from([4u8; 20]);
        let token = Address::ZERO;
        let parent_hash = B256::ZERO;

        // Block 100: addr1 -> addr2 (100 tokens)
        detector.update_profiles_batch(
            100,
            parent_hash,
            &[(token, addr1, addr2, U256::from(100))],
        );

        // Block 101: addr2 -> addr3 (200 tokens)
        detector.update_profiles_batch(
            101,
            parent_hash,
            &[(token, addr2, addr3, U256::from(200))],
        );

        // Block 102: addr3 -> addr4 (300 tokens)
        detector.update_profiles_batch(
            102,
            parent_hash,
            &[(token, addr3, addr4, U256::from(300))],
        );

        // Block 103: addr4 -> addr1 (400 tokens)
        detector.update_profiles_batch(
            103,
            parent_hash,
            &[(token, addr4, addr1, U256::from(400))],
        );

        // Verify initial state
        assert_eq!(detector.motif_detector.block_queue.len(), 4);
        assert_eq!(detector.motif_detector.per_block_edges.len(), 4);
        assert_eq!(detector.motif_detector.graph.node_count(), 4);
        assert_eq!(detector.motif_detector.graph.edge_count(), 4);

        // Reorg scenario:
        // - Block 101: in BOTH (update: addr2 -> addr3 now with 250 tokens instead of 200)
        // - Block 102: ONLY in old (will be removed)
        // - Block 103: in BOTH (update: addr4 -> addr1 now with 450 tokens)
        // - Block 104: ONLY in new (new block: addr1 -> addr3, 500 tokens)

        let old_blocks = vec![101, 102, 103];
        let new_blocks = vec![
            // Block 101: updated transaction
            (101, parent_hash, vec![(token, addr2, addr3, U256::from(250))]),
            // Block 103: updated transaction
            (103, parent_hash, vec![(token, addr4, addr1, U256::from(450))]),
            // Block 104: brand new block
            (104, parent_hash, vec![(token, addr1, addr3, U256::from(500))]),
        ];

        // Execute reorg
        detector.handle_reorg(&old_blocks, &new_blocks);

        // Verify final state
        // Block queue should have: 100, 101, 103, 104 (102 removed)
        assert_eq!(detector.motif_detector.block_queue.len(), 4);
        let queue_vec: Vec<u64> = detector.motif_detector.block_queue.iter().copied().collect();
        assert_eq!(queue_vec, vec![100, 101, 103, 104]);

        // per_block_edges should have entries for 100, 101, 103, 104
        assert_eq!(detector.motif_detector.per_block_edges.len(), 4);
        assert!(detector.motif_detector.per_block_edges.contains_key(&100));
        assert!(detector.motif_detector.per_block_edges.contains_key(&101));
        assert!(!detector.motif_detector.per_block_edges.contains_key(&102)); // Removed
        assert!(detector.motif_detector.per_block_edges.contains_key(&103));
        assert!(detector.motif_detector.per_block_edges.contains_key(&104));

        // Verify edges were updated correctly
        // Block 101: should have 1 edge with amount 250
        let block_101_edges = &detector.motif_detector.per_block_edges[&101];
        assert_eq!(block_101_edges.len(), 1);
        let edge_101 = detector.motif_detector.graph.edge_weight(block_101_edges[0]).unwrap();
        assert_eq!(edge_101.amount, U256::from(250));
        assert_eq!(edge_101.block, 101);

        // Block 103: should have 1 edge with amount 450
        let block_103_edges = &detector.motif_detector.per_block_edges[&103];
        assert_eq!(block_103_edges.len(), 1);
        let edge_103 = detector.motif_detector.graph.edge_weight(block_103_edges[0]).unwrap();
        assert_eq!(edge_103.amount, U256::from(450));
        assert_eq!(edge_103.block, 103);

        // Block 104: should have 1 edge with amount 500
        let block_104_edges = &detector.motif_detector.per_block_edges[&104];
        assert_eq!(block_104_edges.len(), 1);
        let edge_104 = detector.motif_detector.graph.edge_weight(block_104_edges[0]).unwrap();
        assert_eq!(edge_104.amount, U256::from(500));
        assert_eq!(edge_104.block, 104);

        // Total edges should be 4 (blocks 100, 101, 103, 104)
        assert_eq!(detector.motif_detector.graph.edge_count(), 4);

        // All 4 nodes should still exist (no orphans in this case)
        assert_eq!(detector.motif_detector.graph.node_count(), 4);

        println!("{:?}", detector.motif_detector.block_queue);
        println!("✓ All reorg cases validated successfully");
    }

    #[test]
    fn test_reorg_with_orphaned_nodes() {
        // Setup
        let mut detector = AmlEvaluator::new();

        let addr1 = Address::from([1u8; 20]);
        let addr2 = Address::from([2u8; 20]);
        let addr3 = Address::from([3u8; 20]);
        let addr_isolated = Address::from([99u8; 20]); // Will become orphaned
        let token = Address::ZERO;
        let parent_hash = B256::ZERO;

        // Block 100: addr1 -> addr2
        detector.update_profiles_batch(
            100,
            parent_hash,
            &[(token, addr1, addr2, U256::from(100))],
        );

        // Block 101: addr2 -> addr_isolated (this will be removed, orphaning addr_isolated)
        detector.update_profiles_batch(
            101,
            parent_hash,
            &[(token, addr2, addr_isolated, U256::from(200))],
        );

        // Block 102: addr1 -> addr3
        detector.update_profiles_batch(
            102,
            parent_hash,
            &[(token, addr1, addr3, U256::from(300))],
        );

        // Initial state: 4 nodes (addr1, addr2, addr3, addr_isolated)
        assert_eq!(detector.motif_detector.graph.node_count(), 4);

        // Reorg: remove block 101, keep 100 and 102
        let old_blocks = vec![101];
        let new_blocks = vec![]; // Block 101 removed, nothing replaces it

        detector.handle_reorg(&old_blocks, &new_blocks);

        // Block queue should have: 100, 102
        assert_eq!(detector.motif_detector.block_queue.len(), 2);
        let queue_vec: Vec<u64> = detector.motif_detector.block_queue.iter().copied().collect();
        assert_eq!(queue_vec, vec![100, 102]);

        // addr_isolated should be removed (orphaned)
        assert_eq!(detector.motif_detector.graph.node_count(), 3);
        assert!(!detector.motif_detector.node_map.contains_key(&addr_isolated));

        // Other nodes should still exist
        assert!(detector.motif_detector.node_map.contains_key(&addr1));
        assert!(detector.motif_detector.node_map.contains_key(&addr2));
        assert!(detector.motif_detector.node_map.contains_key(&addr3));

        println!("{:?}", detector.motif_detector.block_queue);
        println!("✓ Orphaned node removal validated successfully");
    }

    #[test]
    fn test_reorg_maintains_block_queue_order() {
        // Setup
        let mut detector = AmlEvaluator::new();

        let addr1 = Address::from([1u8; 20]);
        let addr2 = Address::from([2u8; 20]);
        let token = Address::ZERO;
        let parent_hash = B256::ZERO;

        // Add blocks in order: 100, 101, 102, 103, 104
        for block in 100..=104 {
            detector.update_profiles_batch(
                block,
                parent_hash,
                &[(token, addr1, addr2, U256::from(block as u128))],
            );
        }

        // Reorg: remove 102, add 105 and 106
        let old_blocks = vec![102];
        let new_blocks = vec![
            (105, parent_hash, vec![(token, addr1, addr2, U256::from(105))]),
            (106, parent_hash, vec![(token, addr1, addr2, U256::from(106))]),
        ];

        detector.handle_reorg(&old_blocks, &new_blocks);

        // Block queue should be sorted: 100, 101, 103, 104, 105, 106
        let queue_vec: Vec<u64> = detector.motif_detector.block_queue.iter().copied().collect();
        assert_eq!(queue_vec, vec![100, 101, 103, 104, 105, 106]);

        // Verify it's actually sorted
        let mut sorted = queue_vec.clone();
        sorted.sort_unstable();
        assert_eq!(queue_vec, sorted);

        println!("{:?}", detector.motif_detector.block_queue);
        println!("✓ Block queue order maintained correctly");
    }
}
