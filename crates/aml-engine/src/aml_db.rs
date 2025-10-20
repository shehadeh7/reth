use std::collections::{BTreeMap, HashMap};
use alloy_primitives::{Address, FixedBytes, U256};
use bincode::{Encode, Decode, config};
use redb::{Database, ReadableTable, TableDefinition};
use crate::account_profile::{AccountProfile, BlockMetrics, WindowCache};

#[derive(Debug, Clone, Encode, Decode)]
pub struct SerializableU256([u8; 32]);

impl From<U256> for SerializableU256 {
    fn from(u: U256) -> Self {
        Self(u.to_be_bytes()) // big endian 32 bytes
    }
}

impl From<SerializableU256> for U256 {
    fn from(s: SerializableU256) -> Self {
        U256::from_be_bytes(s.0)
    }
}

#[derive(Debug, Clone, Encode, Decode)]
pub struct BlockMetricsDb {
    pub spend_amount: SerializableU256,   // Outbound spend
    pub receive_amount: SerializableU256, // Inbound receive
    pub tx_count: u32,                    // Outbound count (velocity)
}


impl From<&BlockMetrics> for BlockMetricsDb {
    fn from(m: &BlockMetrics) -> Self {
        Self {
            spend_amount: m.spend_amount.into(),
            receive_amount: m.receive_amount.into(),
            tx_count: m.tx_count,
        }
    }
}

impl From<BlockMetricsDb> for BlockMetrics {
    fn from(d: BlockMetricsDb) -> Self {
        Self {
            spend_amount: d.spend_amount.into(),
            receive_amount: d.receive_amount.into(),
            tx_count: d.tx_count,
        }
    }
}


#[derive(Debug, Clone, Encode, Decode)]
pub struct WindowCacheDb {
    pub sum: SerializableU256,         // Outbound sum
    pub inbound_sum: SerializableU256, // Inbound sum
    pub count: u32,                    // Outbound count
}

impl From<&WindowCache> for WindowCacheDb {
    fn from(w: &WindowCache) -> Self {
        Self {
            sum: w.sum.into(),
            inbound_sum: w.inbound_sum.into(),
            count: w.count,
        }
    }
}

impl From<WindowCacheDb> for WindowCache {
    fn from(d: WindowCacheDb) -> Self {
        Self {
            sum: d.sum.into(),
            inbound_sum: d.inbound_sum.into(),
            count: d.count,
        }
    }
}

// possibly move these into another file, integrate with existing aml module, see what to persist
#[derive(Debug, Clone, Encode, Decode)]
pub struct AccountProfileDb {
    address: [u8; 20],

    // block_number => metrics for that block
    pub metrics: HashMap<[u8; 20], BTreeMap<u64, BlockMetricsDb>>,

    // per-window caches; indices must align with `windows`
    pub caches: HashMap<[u8; 20], Vec<WindowCacheDb>>,

    last_update_block: u64,      // Last block number this profile was updated
}

impl From<&AccountProfile> for AccountProfileDb {
    fn from(profile: &AccountProfile) -> Self {
        let metrics = profile.metrics.iter()
            .map(|(&token, blocks)| (
                *token.0.as_ref(),
                blocks.iter().map(|(b, m)| (*b, BlockMetricsDb::from(m))).collect()
            ))
            .collect();

        let caches = profile.caches.iter()
            .map(|(&token, windows)| (
                *token.0.as_ref(),
                windows.iter().map(WindowCacheDb::from).collect()
            ))
            .collect();

        Self {
            address: *profile.address.0.as_ref(),
            metrics,
            caches,
            last_update_block: profile.last_update_block,
        }
    }
}

impl From<AccountProfileDb> for AccountProfile {
    fn from(d: AccountProfileDb) -> Self {
        let metrics = d.metrics.into_iter()
            .map(|(tbytes, blocks)| (
                Address(FixedBytes::from(tbytes)),
                blocks.into_iter().map(|(b, m)| (b, BlockMetrics::from(m))).collect()
            ))
            .collect();

        let caches = d.caches.into_iter()
            .map(|(tbytes, windows)| (
                Address(FixedBytes::from(tbytes)),
                windows.into_iter().map(WindowCache::from).collect()
            ))
            .collect();

        Self {
            address: Address(FixedBytes::from(d.address)),
            metrics,
            caches,
            last_update_block: d.last_update_block,
        }
    }
}

const PROFILES: &str = "profiles";

pub struct AmlDb {
    db: Database,
    profiles: TableDefinition<'static, [u8; 20], Vec<u8>>,
}

impl AmlDb {
    pub fn new(db_path: &str) -> Self {
        let db = Database::create(db_path).unwrap();
        let profiles = TableDefinition::new(PROFILES);

        // Initialize table
        {
            let write_txn = db.begin_write().unwrap();
            write_txn.open_table::<[u8; 20], Vec<u8>>(profiles).unwrap();
            write_txn.commit().unwrap();
        }

        Self { db, profiles }
    }

    pub fn save_profile(&self, profile: &AccountProfileDb) {
        let write_txn = self.db.begin_write().unwrap();
        {
            let mut table = write_txn.open_table(self.profiles).unwrap();
            let config = config::standard();
            let bytes = bincode::encode_to_vec(profile, config).unwrap();
            table.insert(&profile.address, bytes).unwrap();
        }
        write_txn.commit().unwrap();
    }

    pub fn save_profiles_batch(&self, account_profiles: &[AccountProfileDb]) {
        let write_txn = self.db.begin_write().unwrap();
        {
            let mut table = write_txn.open_table(self.profiles).unwrap();
            let config = config::standard();
            for profile in account_profiles {
                let bytes = bincode::encode_to_vec(profile, config).unwrap();
                table.insert(&profile.address, bytes).unwrap();
            }
        }
        write_txn.commit().unwrap();
    }

    pub fn load_profile(&self, address: &Address) -> Option<AccountProfileDb> {
        let txn = self.db.begin_read().unwrap();
        let table = txn.open_table(self.profiles).unwrap();

        if let Some(bytes) = table.get(&address.0).unwrap() {
            let config = config::standard();
            Some(
                bincode::decode_from_slice::<AccountProfileDb, _>(&*bytes.value(), config)
                    .unwrap()
                    .0,
            )
        } else {
            None
        }
    }

    /// Load all profiles from DB (Intended for testing purposes)
    pub fn load_all_profiles(&self) -> Vec<(Address, AccountProfileDb)> {
        let txn = self.db.begin_read().unwrap();
        let table = txn.open_table(self.profiles).unwrap();
        let config = config::standard();

        // Iterate over all key-value pairs
        table.iter().unwrap()
            .map(|entry| {
                let (key, value) = entry.unwrap();
                let addr = Address(key.value().try_into().unwrap());
                let profile: AccountProfileDb =
                    bincode::decode_from_slice::<AccountProfileDb, _>(&*value.value(), config)
                        .unwrap()
                        .0;
                (addr, profile)
            })
            .collect()
    }

    pub fn delete_profile(&self, address: &Address) {
        let write_txn = self.db.begin_write().expect("Failed to begin write transaction");
        {
            let mut table = write_txn
                .open_table(self.profiles)
                .expect("Failed to open profiles table");
            table.remove(&address.0).expect("Failed to delete profile");
        }
        write_txn.commit().expect("Failed to commit profile deletion");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{Address, U256};
    use std::collections::{BTreeMap, HashMap};
    use std::time::Instant;
    use tempfile::tempdir;

    // Keep this in sync with your module’s const
    const WINDOWS: &[u64] = &[7_200, 50_400, 216_000];

    // ---------------- Helpers ----------------

    fn addr(byte: u8) -> Address {
        Address::repeat_byte(byte)
    }

    /// Keep TempDir alive for the test scope so the DB path is not deleted early.
    fn new_db() -> (AmlDb, tempfile::TempDir) {
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("aml_db");
        let db = AmlDb::new(db_path.to_str().unwrap());
        (db, dir)
    }

    fn mk_block_metrics(
        spend: u128,
        receive: u128,
        tx_count: u32,
    ) -> BlockMetrics {
        BlockMetrics {
            spend_amount: U256::from(spend),
            receive_amount: U256::from(receive),
            tx_count,
        }
    }

    fn mk_cache(sum: u128, inbound_sum: u128, count: u32) -> WindowCache {
        WindowCache {
            sum: U256::from(sum),
            inbound_sum: U256::from(inbound_sum),
            count,
        }
    }

    fn assert_u256_eq(a: U256, b: U256, lbl: &str) {
        assert_eq!(a, b, "{lbl} U256 mismatch: left={a}, right={b}");
    }

    fn assert_maps_eq(a: &HashMap<Address, u32>, b: &HashMap<Address, u32>, label: &str) {
        assert_eq!(a.len(), b.len(), "{label} size differs");
        for (k, av) in a {
            let bv = b.get(k).copied();
            assert_eq!(Some(*av), bv, "{label} entry mismatch at {k:?}");
        }
    }

    fn assert_block_metrics_eq(a: &BlockMetrics, b: &BlockMetrics) {
        assert_u256_eq(a.spend_amount, b.spend_amount, "spend_amount");
        assert_u256_eq(a.receive_amount, b.receive_amount, "receive_amount");
        assert_eq!(a.tx_count, b.tx_count, "tx_count mismatch");
    }

    fn assert_cache_eq(a: &WindowCache, b: &WindowCache) {
        assert_u256_eq(a.sum, b.sum, "cache.sum");
        assert_u256_eq(a.inbound_sum, b.inbound_sum, "cache.inbound_sum");
        assert_eq!(a.count, b.count, "cache.count mismatch");
    }

    fn assert_profile_eq(a: &AccountProfile, b: &AccountProfile) {
        assert_eq!(a.address, b.address, "address mismatch");
        assert_eq!(a.last_update_block, b.last_update_block, "last_update_block mismatch");

        // metrics: token -> blocks
        assert_eq!(a.metrics.len(), b.metrics.len(), "metrics length mismatch");
        for (&token, token_metrics_a) in &a.metrics {
            let token_metrics_b = b.metrics.get(&token).expect("missing token in loaded metrics");

            assert_eq!(token_metrics_a.len(), token_metrics_b.len(), "token metrics length mismatch");
            for (blk, ma) in token_metrics_a {
                let mb = token_metrics_b.get(blk).expect("missing block in loaded metrics");
                assert_block_metrics_eq(ma, mb);
            }
        }

        // caches: token -> windows
        assert_eq!(a.caches.len(), b.caches.len(), "caches length mismatch");
        for (&token, token_caches_a) in &a.caches {
            let token_caches_b = b.caches.get(&token).expect("missing token in loaded caches");

            assert_eq!(token_caches_a.len(), token_caches_b.len(), "token caches length mismatch");
            assert_eq!(token_caches_a.len(), WINDOWS.len(), "caches/windows length mismatch");
            for (ca, cb) in token_caches_a.iter().zip(token_caches_b.iter()) {
                assert_cache_eq(ca, cb);
            }
        }
    }

    // ---------------- Tests ----------------

    #[test]
    fn test_save_load_profile_roundtrip() {
        let (db, _tmp) = new_db();

        // Build runtime profile
        let mut metrics = BTreeMap::new();
        metrics.insert(
            20_000_000u64,
            mk_block_metrics(
                300_000,   // spend
                100_000,   // receive
                3,         // tx_count
            ),
        );
        metrics.insert(
            19_950_000u64,
            mk_block_metrics(
                210_100,
                25_000,
                1,
            ),
        );

        let caches = vec![
            // daily
            mk_cache(300_000, 100_000, 3),
            // weekly
            mk_cache(510_100, 125_000, 4),
            // monthly
            mk_cache(510_100, 125_000, 4),
        ];

        let metrics_map = HashMap::from([
            (addr(0), metrics)
        ]);
        let cache_map = HashMap::from([
            (addr(0), caches)
        ]);

        let profile = AccountProfile {
            address: addr(1),
            metrics: metrics_map,
            caches: cache_map,
            last_update_block: 20_000_000,
        };

        // Save → Load → Convert back to runtime
        let db_profile: AccountProfileDb = (&profile).into();
        db.save_profile(&db_profile);

        let loaded_db = db.load_profile(&addr(1)).expect("Failed to load profile");
        let loaded_profile: AccountProfile = loaded_db.into();

        assert_profile_eq(&profile, &loaded_profile);
    }

    #[test]
    fn test_save_profiles_batch_roundtrip() {
        let (db, _tmp) = new_db();

        // Profile 1
        let mut m1 = BTreeMap::new();
        m1.insert(20_000_000u64, mk_block_metrics(111, 222, 1));
        let metrics_map = HashMap::from([
            (addr(0), m1)
        ]);
        let cache_map = HashMap::from([
            (addr(0), vec![
                mk_cache(111, 222, 1),
                mk_cache(111, 222, 1),
                mk_cache(111, 222, 1),
            ])
        ]);
        let p1 = AccountProfile {
            address: addr(1),
            metrics: metrics_map,
            caches: cache_map,
            last_update_block: 20_000_000,
        };

        // Profile 2
        let mut m2 = BTreeMap::new();
        m2.insert(19_123_456u64, mk_block_metrics(999_999, 0, 2));
        m2.insert(19_123_999u64, mk_block_metrics(1, 2, 1));
        let m2_map = HashMap::from([
            (addr(0), m2)
        ]);
        let cache2_map = HashMap::from([
            (addr(0), vec![
                mk_cache(1, 2, 1),
                mk_cache(1_000_000, 2, 3),
                mk_cache(1_000_000, 2, 3),
            ])
        ]);
        let p2 = AccountProfile {
            address: addr(2),
            metrics: m2_map,
            caches: cache2_map,
            last_update_block: 19_124_000,
        };

        let d1: AccountProfileDb = (&p1).into();
        let d2: AccountProfileDb = (&p2).into();

        // Batch save
        db.save_profiles_batch(&[d1.clone(), d2.clone()]);

        // Load and compare
        let l1: AccountProfile = db.load_profile(&addr(1)).unwrap().into();
        let l2: AccountProfile = db.load_profile(&addr(2)).unwrap().into();

        assert_profile_eq(&p1, &l1);
        assert_profile_eq(&p2, &l2);
    }

    #[test]
    fn test_save_profiles_batch_roundtrip_timed() {
        let (db, _tmp) = new_db();

        // Profile 1
        let mut m1 = BTreeMap::new();
        m1.insert(20_000_000u64, mk_block_metrics(111, 222, 1));
        let metrics_map = HashMap::from([
            (addr(0), m1)
        ]);
        let cache_map = HashMap::from([
            (addr(0), vec![
                mk_cache(111, 222, 1),
                mk_cache(111, 222, 1),
                mk_cache(111, 222, 1),
            ])
        ]);
        let p1 = AccountProfile {
            address: addr(1),
            metrics: metrics_map,
            caches: cache_map,
            last_update_block: 20_000_000,
        };

        // Profile 2
        let mut m2 = BTreeMap::new();
        m2.insert(19_123_456u64, mk_block_metrics(999_999, 0, 2));
        m2.insert(19_123_999u64, mk_block_metrics(1, 2, 1));
        let m2_map = HashMap::from([
            (addr(0), m2)
        ]);
        let cache_map = HashMap::from([
            (addr(0), vec![
                mk_cache(1, 2, 1),
                mk_cache(1_000_000, 2, 3),
                mk_cache(1_000_000, 2, 3),
            ])
        ]);
        let p2 = AccountProfile {
            address: addr(2),
            metrics: m2_map,
            caches: cache_map,
            last_update_block: 19_124_000,
        };

        let d1: AccountProfileDb = (&p1).into();
        let d2: AccountProfileDb = (&p2).into();

        // --- measure batch write ---
        let start_write = Instant::now();
        db.save_profiles_batch(&[d1.clone(), d2.clone()]);
        let write_duration = start_write.elapsed();
        println!("DB batch write took {:?}", write_duration);

        // --- measure individual reads ---
        let start_read1 = Instant::now();
        let l1: AccountProfile = db.load_profile(&addr(1)).unwrap().into();
        let read1 = start_read1.elapsed();

        let start_read2 = Instant::now();
        let l2: AccountProfile = db.load_profile(&addr(2)).unwrap().into();
        let read2 = start_read2.elapsed();

        println!("DB read (profile 1) took {:?}", read1);
        println!("DB read (profile 2) took {:?}", read2);

        assert_profile_eq(&p1, &l1);
        assert_profile_eq(&p2, &l2);

        println!(
            "Summary: total = {:?} (write: {:?}, read1: {:?}, read2: {:?})",
            write_duration + read1 + read2,
            write_duration,
            read1,
            read2
        );
    }

    #[test]
    fn test_blockmetrics_maps_roundtrip() {
        let (db, _tmp) = new_db();

        let mut metrics = BTreeMap::new();
        metrics.insert(
            77u64,
            mk_block_metrics(
                1_234_567,
                765_432,
                5,
            ),
        );
        let metrics_map = HashMap::from([
            (addr(0), metrics)
        ]);
        let cache_map = HashMap::from([
            (addr(0), vec![
                mk_cache(1_234_567, 765_432, 5),
                mk_cache(1_234_567, 765_432, 5),
                mk_cache(1_234_567, 765_432, 5),
            ])
        ]);

        let profile = AccountProfile {
            address: addr(0xFF),
            metrics: metrics_map,
            caches: cache_map,
            last_update_block: 77,
        };

        db.save_profile(&AccountProfileDb::from(&profile));

        let loaded: AccountProfile = db.load_profile(&addr(0xFF)).unwrap().into();

        // Deep compare
        assert_profile_eq(&profile, &loaded);
    }

    #[test]
    fn test_delete_profile() {
        let (db, _tmp) = new_db();

        let mut metrics = BTreeMap::new();
        metrics.insert(123u64, mk_block_metrics(42, 0, 1));
        let metrics_map = HashMap::from([
            (addr(0), metrics)
        ]);
        let cache_map = HashMap::from([
            (addr(0), vec![
                mk_cache(42, 0, 1),
                mk_cache(42, 0, 1),
                mk_cache(42, 0, 1),
            ])
        ]);
        let profile = AccountProfile {
            address: addr(7),
            metrics: metrics_map,
            caches: cache_map,
            last_update_block: 123,
        };

        db.save_profile(&AccountProfileDb::from(&profile));

        db.delete_profile(&addr(7));

        let none = db.load_profile(&addr(7));
        assert!(none.is_none(), "profile should be deleted");
    }
}
