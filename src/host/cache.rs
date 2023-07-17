use crate::host::kvpair::MerkleRecord;
use std::collections::BTreeMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    pub static ref MERKLE_CACHE: Mutex<BTreeMap<(u32, [u8; 32]), Option<MerkleRecord>>> = Mutex::new(BTreeMap::new());
}
