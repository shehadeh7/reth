use std::collections::{BTreeMap};
use alloy_primitives::{Address, FixedBytes, U256};
use bincode::{Encode, Decode, config};
use redb::{Database, TableDefinition};
use crate::account_profile::AccountProfile;

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

// possibly move these into another file, integrate with existing aml module, see what to persist
#[derive(Debug, Clone, Encode, Decode)]
pub struct AccountProfileDb {
    address: [u8; 20],
    spends: BTreeMap<u64, SerializableU256>, // block_number => total spent in that block
    daily_sum: SerializableU256,             // Cached sum for last 7,200 blocks
    weekly_sum: SerializableU256,            // Cached sum for last 50,400 blocks
    monthly_sum: SerializableU256,           // Cached sum for last 216,000 blocks
    last_update_block: u64,      // Last block number this profile was updated
}

impl From<&AccountProfile> for AccountProfileDb {
    fn from(profile: &AccountProfile) -> Self {
        Self {
            address: *profile.address.0.as_ref(),
            spends: profile
                .spends
                .iter()
                .map(|(&block, &amount)| (block, amount.into()))
                .collect(),
            daily_sum: profile.daily_sum.into(),
            weekly_sum: profile.weekly_sum.into(),
            monthly_sum: profile.monthly_sum.into(),
            last_update_block: profile.last_update_block,
        }
    }
}

impl From<AccountProfileDb> for AccountProfile {
    fn from(db: AccountProfileDb) -> Self {
        Self {
            address: Address(FixedBytes::from(db.address)),
            spends: db
                .spends
                .into_iter()
                .map(|(block, amount)| (block, amount.into()))
                .collect(),
            daily_sum: db.daily_sum.into(),
            weekly_sum: db.weekly_sum.into(),
            monthly_sum: db.monthly_sum.into(),
            last_update_block: db.last_update_block,
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
    use tempfile::tempdir;
    use alloy_primitives::{Address, U256};
    use std::collections::BTreeMap;

    const DAILY_WINDOW_BLOCKS: u64 = 7_200;   // ~1 day at 12s/block
    const WEEKLY_WINDOW_BLOCKS: u64 = 50_400; // ~1 week
    const MONTHLY_WINDOW_BLOCKS: u64 = 216_000; // ~30 days

    fn addr(byte: u8) -> Address {
        // helper to make dummy addresses like 0x000..01, 0x000..02, etc.
        Address::repeat_byte(byte)
    }

    fn new_db() -> AmlDb {
        // temp dir to avoid writing to real DB
        let dir = tempdir().unwrap();
        let db_path = dir.path().join("aml_db");
        AmlDb::new(db_path.to_str().unwrap())
    }

    #[test]
    fn test_save_load_profile() {
        let db = new_db();

        // Create an AccountProfile
        let mut spends = BTreeMap::new();
        spends.insert(19_950_000, U256::from(300_000));
        spends.insert(20_000_000, U256::from(210_100));
        let bo_profile = AccountProfile {
            address: addr(1),
            spends,
            daily_sum: U256::from(210_100),    // Only block 20_000_000 in daily window
            weekly_sum: U256::from(210_100),   // Only block 20_000_000 in weekly window
            monthly_sum: U256::from(510_100),  // Both blocks in monthly window
            last_update_block: 20_000_000,
        };

        let db_profile: AccountProfileDb = AccountProfileDb::from(&bo_profile); // implement From<BO> for DB

        // Save to DB
        db.save_profile(&db_profile);

        // Load back from DB
        let loaded = db.load_profile(&addr(1)).expect("Failed to load profile");

        // Compare fields
        assert_eq!(loaded.address, bo_profile.address);
        assert_eq!(Into::<U256>::into(loaded.daily_sum), bo_profile.daily_sum);
        assert_eq!(Into::<U256>::into(loaded.weekly_sum), bo_profile.weekly_sum);
        assert_eq!(Into::<U256>::into(loaded.monthly_sum), bo_profile.monthly_sum);
        assert_eq!(loaded.last_update_block, bo_profile.last_update_block);
    }

    #[test]
    fn test_save_profiles_batch() {
        let db = new_db();

        // Create two AccountProfiles
        let mut spends1 = BTreeMap::new();
        spends1.insert(19_950_000, U256::from(300_000));
        spends1.insert(20_000_000, U256::from(210_100));
        let bo_profile1 = AccountProfile {
            address: addr(1),
            spends: spends1,
            daily_sum: U256::from(210_100),
            weekly_sum: U256::from(210_100),
            monthly_sum: U256::from(510_100),
            last_update_block: 20_000_000,
        };

        let mut spends2 = BTreeMap::new();
        spends2.insert(19_999_000, U256::from(100_000));
        spends2.insert(20_000_000, U256::from(200_000));
        let bo_profile2 = AccountProfile {
            address: addr(2),
            spends: spends2,
            daily_sum: U256::from(200_000),
            weekly_sum: U256::from(300_000),
            monthly_sum: U256::from(300_000),
            last_update_block: 20_000_000,
        };

        let db_profile1 = AccountProfileDb::from(&bo_profile1);
        let db_profile2 = AccountProfileDb::from(&bo_profile2);

        // Save batch to DB
        db.save_profiles_batch(&[db_profile1.clone(), db_profile2.clone()]);

        // Load back from DB
        let loaded1 = db.load_profile(&addr(1)).expect("Failed to load profile 1");
        let loaded2 = db.load_profile(&addr(2)).expect("Failed to load profile 2");

        // Compare fields for profile 1
        assert_eq!(loaded1.address, bo_profile1.address);
        assert_eq!(Into::<U256>::into(loaded1.daily_sum), bo_profile1.daily_sum);
        assert_eq!(Into::<U256>::into(loaded1.weekly_sum), bo_profile1.weekly_sum);
        assert_eq!(Into::<U256>::into(loaded1.monthly_sum), bo_profile1.monthly_sum);
        assert_eq!(loaded1.last_update_block, bo_profile1.last_update_block);

        // Compare fields for profile 2
        assert_eq!(loaded2.address, bo_profile2.address);
        assert_eq!(Into::<U256>::into(loaded2.daily_sum), bo_profile2.daily_sum);
        assert_eq!(Into::<U256>::into(loaded2.weekly_sum), bo_profile2.weekly_sum);
        assert_eq!(Into::<U256>::into(loaded2.monthly_sum), bo_profile2.monthly_sum);
        assert_eq!(loaded2.last_update_block, bo_profile2.last_update_block);
    }

    #[test]
    fn test_prune_and_save_load() {
        let db = new_db();

        // Create a profile with old and recent spends
        let mut spends = BTreeMap::new();
        spends.insert(19_700_000, U256::from(500_000)); // Outside monthly window
        spends.insert(19_950_000, U256::from(300_000)); // Inside monthly window
        spends.insert(20_000_000, U256::from(210_100)); // Recent
        let mut bo_profile = AccountProfile {
            address: addr(1),
            spends,
            daily_sum: U256::from(0),
            weekly_sum: U256::from(210_100),
            monthly_sum: U256::from(510_100), // Initially incorrect, will be fixed by prune
            last_update_block: 20_000_000,
        };

        // Prune spends outside monthly window
        bo_profile.prune_old(20_000_000, MONTHLY_WINDOW_BLOCKS);

        println!("{:#?}", bo_profile);

        // Verify pruning
        assert!(!bo_profile.spends.contains_key(&19_700_000)); // Pruned
        assert!(bo_profile.spends.contains_key(&19_950_000)); // Kept
        assert!(bo_profile.spends.contains_key(&20_000_000)); // Kept
        assert_eq!(bo_profile.daily_sum, U256::from(210_100));
        assert_eq!(bo_profile.weekly_sum, U256::from(510_100));
        assert_eq!(bo_profile.monthly_sum, U256::from(510_100)); // 300_000 + 210_100

        let db_profile = AccountProfileDb::from(&bo_profile);

        // Save to DB
        db.save_profile(&db_profile);

        // Load back
        let loaded = db.load_profile(&addr(1)).expect("Failed to load profile");

        // Compare
        assert_eq!(loaded.address, bo_profile.address);
        assert_eq!(loaded.spends.len(), bo_profile.spends.len());
        assert_eq!(Into::<U256>::into(loaded.daily_sum), bo_profile.daily_sum);
        assert_eq!(Into::<U256>::into(loaded.weekly_sum), bo_profile.weekly_sum);
        assert_eq!(Into::<U256>::into(loaded.monthly_sum), bo_profile.monthly_sum);
        assert_eq!(loaded.last_update_block, bo_profile.last_update_block);
    }

    #[test]
    fn test_delete_profile() {
        let db = new_db();

        // Create a profile
        let mut spends = BTreeMap::new();
        spends.insert(19_950_000, U256::from(300_000));
        let bo_profile = AccountProfile {
            address: addr(1),
            spends,
            daily_sum: U256::from(0),
            weekly_sum: U256::from(300_000),
            monthly_sum: U256::from(300_000),
            last_update_block: 20_000_000,
        };

        let db_profile: AccountProfileDb = AccountProfileDb::from(&bo_profile);

        // Save to DB
        db.save_profile(&db_profile);

        // Delete from DB
        db.delete_profile(&addr(1));

        // Verify profile is gone
        let loaded = db.load_profile(&addr(1));
        assert!(loaded.is_none());
    }
}
