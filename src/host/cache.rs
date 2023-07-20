use crate::host::kvpair::MerkleRecord;
use lru::LruCache;
use std::num::NonZeroUsize;
use std::sync::Mutex;

const DEFAULT_CACHE_SIZE: usize = 100000;

lazy_static::lazy_static! {
    pub static ref MERKLE_CACHE: Mutex<LruCache<String, MerkleRecord>> =
        Mutex::new(LruCache::<String, MerkleRecord>::new(
            NonZeroUsize::new(DEFAULT_CACHE_SIZE).unwrap(),
        ));
}
