use std::collections::VecDeque;
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
    pub address: [u8; 20],
    pub sent_amounts: VecDeque<(u64, SerializableU256)>,
    pub recv_amounts: VecDeque<(u64, SerializableU256)>,
    pub total_sent: SerializableU256,
    pub total_received: SerializableU256,
}

impl From<&AccountProfile> for AccountProfileDb {
    fn from(profile: &AccountProfile) -> Self {
        Self {
            address: *profile.address.0.as_ref(),
            sent_amounts: profile.sent_amounts.iter().map(|(b, u)| (*b, (*u).into())).collect(),
            recv_amounts: profile.recv_amounts.iter().map(|(b, u)| (*b, (*u).into())).collect(),
            total_sent: profile.total_sent.into(),
            total_received: profile.total_received.into(),
        }
    }
}

impl From<AccountProfileDb> for AccountProfile {
    fn from(db: AccountProfileDb) -> Self {
        Self {
            address: Address(FixedBytes::from(db.address)),
            sent_amounts: db.sent_amounts.into_iter().map(|(b, u)| (b, u.into())).collect(),
            recv_amounts: db.recv_amounts.into_iter().map(|(b, u)| (b, u.into())).collect(),
            total_sent: db.total_sent.into(),
            total_received: db.total_received.into(),
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use alloy_primitives::Address;

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

        // Create a BO profile (simulating the real business object)
        let bo_profile = AccountProfile {
            address: addr(1),
            sent_amounts: Default::default(),
            recv_amounts: Default::default(),
            total_sent: U256::from(100),
            total_received: U256::from(50),
        };

        // Convert BO -> DB profile
        let db_profile: AccountProfileDb = AccountProfileDb::from(&bo_profile); // implement From<BO> for DB

        db.save_profile(&db_profile);

        // Load back from DB
        let loaded = db.load_profile(&addr(1)).unwrap();

        // Compare fields
        assert_eq!(Into::<U256>::into(loaded.total_sent), bo_profile.total_sent);
        assert_eq!(Into::<U256>::into(loaded.total_received), bo_profile.total_received);
        assert_eq!(loaded.address, bo_profile.address.0);
    }

    #[test]
    fn test_save_profiles_batch() {
        let db = new_db();

        // Create a BO profile (simulating the real business object)
        let bo_profile = AccountProfile {
            address: addr(1),
            sent_amounts: Default::default(),
            recv_amounts: Default::default(),
            total_sent: U256::from(100),
            total_received: U256::from(50),
        };
        let bo_profile_2 = AccountProfile {
            address: addr(2),
            sent_amounts: VecDeque::from([(1, U256::from(100)), (2, U256::from(200))]),
            recv_amounts: VecDeque::from([(1, U256::from(50)), (3, U256::from(150))]),
            total_sent: U256::from(1000),
            total_received: U256::from(50),
        };

        // Convert BO -> DB profile
        let db_profile: AccountProfileDb = AccountProfileDb::from(&bo_profile); // implement From<BO> for DB
        let db_profile_2: AccountProfileDb = AccountProfileDb::from(&bo_profile_2);

        db.save_profiles_batch(&vec![db_profile, db_profile_2]);

        // Load back from DB
        let loaded = db.load_profile(&addr(1)).unwrap();
        let loaded_2 = db.load_profile(&addr(2)).unwrap();

        // Compare fields
        assert_eq!(Into::<U256>::into(loaded.total_sent), bo_profile.total_sent);
        assert_eq!(Into::<U256>::into(loaded.total_received), bo_profile.total_received);
        assert_eq!(loaded.address, bo_profile.address.0);
        assert_eq!(Into::<U256>::into(loaded_2.total_sent), bo_profile_2.total_sent);
        assert_eq!(Into::<U256>::into(loaded_2.total_received), bo_profile_2.total_received);
        assert_eq!(loaded_2.address, bo_profile_2.address.0);

        // Compare sent_amounts entry by entry
        assert_eq!(loaded.sent_amounts.len(), bo_profile.sent_amounts.len());
        for ((block_l, amt_l), (block_b, amt_b)) in
            loaded.sent_amounts.iter().zip(bo_profile.sent_amounts.iter())
        {
            assert_eq!(*block_l, *block_b);
            assert_eq!(Into::<U256>::into(amt_l.clone()), *amt_b);
        }

        for ((block_l, amt_l), (block_b, amt_b)) in
            loaded.recv_amounts.iter().zip(bo_profile.recv_amounts.iter())
        {
            assert_eq!(*block_l, *block_b);
            assert_eq!(Into::<U256>::into(amt_l.clone()), *amt_b);
        }
    }
}
