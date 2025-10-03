use std::collections::{BTreeMap, HashMap};
use alloy_primitives::{Address, FixedBytes, U256};
use bincode::{Encode, Decode, config};
use redb::{Database, TableDefinition};
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
    // Store maps as Vec<(addr, count)> for stable encoding
    pub recipients: Vec<([u8; 20], u32)>, // Outbound fan-out (addr => count in block)
    pub senders: Vec<([u8; 20], u32)>,    // Inbound fan-in  (addr => count in block)
}


impl From<&BlockMetrics> for BlockMetricsDb {
    fn from(m: &BlockMetrics) -> Self {
        Self {
            spend_amount: m.spend_amount.into(),
            receive_amount: m.receive_amount.into(),
            tx_count: m.tx_count,
            recipients: m.recipients.iter()
                .map(|(a, c)| (*a.0.as_ref(), *c))
                .collect(),
            senders: m.senders.iter()
                .map(|(a, c)| (*a.0.as_ref(), *c))
                .collect(),
        }
    }
}

impl From<BlockMetricsDb> for BlockMetrics {
    fn from(d: BlockMetricsDb) -> Self {
        let recipients: HashMap<Address, u32> = d.recipients
            .into_iter()
            .map(|(b, c)| (Address(FixedBytes::from(b)), c))
            .collect();

        let senders: HashMap<Address, u32> = d.senders
            .into_iter()
            .map(|(b, c)| (Address(FixedBytes::from(b)), c))
            .collect();

        Self {
            spend_amount: d.spend_amount.into(),
            receive_amount: d.receive_amount.into(),
            tx_count: d.tx_count,
            recipients,
            senders,
        }
    }
}


#[derive(Debug, Clone, Encode, Decode)]
pub struct WindowCacheDb {
    pub sum: SerializableU256,         // Outbound sum
    pub inbound_sum: SerializableU256, // Inbound sum
    pub count: u32,                    // Outbound count
    pub unique_out: u32,               // Fan-out (avoid usize on disk)
    pub unique_in: u32,                // Fan-in
}

impl From<&WindowCache> for WindowCacheDb {
    fn from(w: &WindowCache) -> Self {
        Self {
            sum: w.sum.into(),
            inbound_sum: w.inbound_sum.into(),
            count: w.count,
            unique_out: w.unique_out as u32,
            unique_in: w.unique_in as u32,
        }
    }
}

impl From<WindowCacheDb> for WindowCache {
    fn from(d: WindowCacheDb) -> Self {
        Self {
            sum: d.sum.into(),
            inbound_sum: d.inbound_sum.into(),
            count: d.count,
            unique_out: d.unique_out as usize,
            unique_in: d.unique_in as usize,
        }
    }
}

// possibly move these into another file, integrate with existing aml module, see what to persist
#[derive(Debug, Clone, Encode, Decode)]
pub struct AccountProfileDb {
    address: [u8; 20],

    // block_number => metrics for that block
    pub metrics: BTreeMap<u64, BlockMetricsDb>,

    // per-window caches; indices must align with `windows`
    pub caches: Vec<WindowCacheDb>,

    last_update_block: u64,      // Last block number this profile was updated
}

impl From<&AccountProfile> for AccountProfileDb {
    fn from(profile: &AccountProfile) -> Self {

        // Convert BTreeMap<u64, BlockMetrics> -> BTreeMap<u64, BlockMetricsDb>
        let metrics = profile.metrics.iter()
            .map(|(blk, m)| (*blk, BlockMetricsDb::from(m)))
            .collect::<BTreeMap<_, _>>();

        let caches = profile.caches.iter()
            .map(WindowCacheDb::from)
            .collect::<Vec<_>>();

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
            .map(|(blk, mdb)| (blk, BlockMetrics::from(mdb)))
            .collect::<BTreeMap<_, _>>();

        let caches = d.caches.into_iter()
            .map(WindowCache::from)
            .collect::<Vec<_>>();


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
        recipients: &[(u8, u32)],
        senders: &[(u8, u32)],
    ) -> BlockMetrics {
        let mut r: HashMap<Address, u32> = HashMap::new();
        let mut s: HashMap<Address, u32> = HashMap::new();
        for (b, c) in recipients {
            r.insert(addr(*b), *c);
        }
        for (b, c) in senders {
            s.insert(addr(*b), *c);
        }
        BlockMetrics {
            spend_amount: U256::from(spend),
            receive_amount: U256::from(receive),
            tx_count,
            recipients: r,
            senders: s,
        }
    }

    fn mk_cache(sum: u128, inbound_sum: u128, count: u32, unique_out: u32, unique_in: u32) -> WindowCache {
        WindowCache {
            sum: U256::from(sum),
            inbound_sum: U256::from(inbound_sum),
            count,
            unique_out: unique_out as usize,
            unique_in: unique_in as usize,
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
        assert_maps_eq(&a.recipients, &b.recipients, "recipients");
        assert_maps_eq(&a.senders, &b.senders, "senders");
    }

    fn assert_cache_eq(a: &WindowCache, b: &WindowCache) {
        assert_u256_eq(a.sum, b.sum, "cache.sum");
        assert_u256_eq(a.inbound_sum, b.inbound_sum, "cache.inbound_sum");
        assert_eq!(a.count, b.count, "cache.count mismatch");
        assert_eq!(a.unique_out, b.unique_out, "cache.unique_out mismatch");
        assert_eq!(a.unique_in, b.unique_in, "cache.unique_in mismatch");
    }

    fn assert_profile_eq(a: &AccountProfile, b: &AccountProfile) {
        assert_eq!(a.address, b.address, "address mismatch");
        assert_eq!(a.last_update_block, b.last_update_block, "last_update_block mismatch");

        // metrics
        assert_eq!(a.metrics.len(), b.metrics.len(), "metrics length mismatch");
        for (blk, ma) in &a.metrics {
            let mb = b.metrics.get(blk).expect("missing block in loaded metrics");
            assert_block_metrics_eq(ma, mb);
        }

        // caches
        assert_eq!(a.caches.len(), b.caches.len(), "caches length mismatch");
        assert_eq!(a.caches.len(), WINDOWS.len(), "caches/windows length mismatch");
        for (ca, cb) in a.caches.iter().zip(b.caches.iter()) {
            assert_cache_eq(ca, cb);
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
                &[(2, 2), (3, 1)], // recipients
                &[(9, 3)],         // senders
            ),
        );
        metrics.insert(
            19_950_000u64,
            mk_block_metrics(
                210_100,
                25_000,
                1,
                &[(4, 1)],
                &[(8, 1)],
            ),
        );

        let caches = vec![
            // daily
            mk_cache(300_000, 100_000, 3, 2, 1),
            // weekly
            mk_cache(510_100, 125_000, 4, 3, 2),
            // monthly
            mk_cache(510_100, 125_000, 4, 3, 2),
        ];

        let profile = AccountProfile {
            address: addr(1),
            metrics,
            caches,
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
        m1.insert(20_000_000u64, mk_block_metrics(111, 222, 1, &[(0xAA, 1)], &[(0xBB, 1)]));
        let p1 = AccountProfile {
            address: addr(1),
            metrics: m1,
            caches: vec![
                mk_cache(111, 222, 1, 1, 1),
                mk_cache(111, 222, 1, 1, 1),
                mk_cache(111, 222, 1, 1, 1),
            ],
            last_update_block: 20_000_000,
        };

        // Profile 2
        let mut m2 = BTreeMap::new();
        m2.insert(19_123_456u64, mk_block_metrics(999_999, 0, 2, &[(0x01, 2)], &[]));
        m2.insert(19_123_999u64, mk_block_metrics(1, 2, 1, &[(0x02, 1)], &[(0x03, 1)]));
        let p2 = AccountProfile {
            address: addr(2),
            metrics: m2,
            caches: vec![
                mk_cache(1, 2, 1, 1, 1),
                mk_cache(1_000_000, 2, 3, 2, 1),
                mk_cache(1_000_000, 2, 3, 2, 1),
            ],
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
    fn test_blockmetrics_maps_roundtrip() {
        let (db, _tmp) = new_db();

        let mut metrics = BTreeMap::new();
        metrics.insert(
            77u64,
            mk_block_metrics(
                1_234_567,
                765_432,
                5,
                &[(0x10, 1), (0x11, 2), (0x12, 2)],
                &[(0xA0, 3), (0xA1, 1), (0xA2, 1)],
            ),
        );

        let profile = AccountProfile {
            address: addr(0xFF),
            metrics,
            caches: vec![
                mk_cache(1_234_567, 765_432, 5, 3, 3),
                mk_cache(1_234_567, 765_432, 5, 3, 3),
                mk_cache(1_234_567, 765_432, 5, 3, 3),
            ],
            last_update_block: 77,
        };

        db.save_profile(&AccountProfileDb::from(&profile));

        let loaded: AccountProfile = db.load_profile(&addr(0xFF)).unwrap().into();

        // Deep compare
        assert_profile_eq(&profile, &loaded);

        // Extra checks on maps
        let bm = loaded.metrics.get(&77).unwrap();
        assert_eq!(bm.recipients.get(&addr(0x11)).copied(), Some(2));
        assert_eq!(bm.senders.get(&addr(0xA2)).copied(), Some(1));
    }

    #[test]
    fn test_delete_profile() {
        let (db, _tmp) = new_db();

        let mut metrics = BTreeMap::new();
        metrics.insert(123u64, mk_block_metrics(42, 0, 1, &[(0x01,1)], &[]));
        let profile = AccountProfile {
            address: addr(7),
            metrics,
            caches: vec![
                mk_cache(42, 0, 1, 1, 0),
                mk_cache(42, 0, 1, 1, 0),
                mk_cache(42, 0, 1, 1, 0),
            ],
            last_update_block: 123,
        };

        db.save_profile(&AccountProfileDb::from(&profile));

        db.delete_profile(&addr(7));

        let none = db.load_profile(&addr(7));
        assert!(none.is_none(), "profile should be deleted");
    }
}
