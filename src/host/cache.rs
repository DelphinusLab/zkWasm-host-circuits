use crate::host::datahash::DataHashRecord;
use crate::host::mongomerkle::MerkleRecord;
use lru::LruCache;
use std::num::NonZeroUsize;
use std::sync::Mutex;

// If maxsize is set to None, the LRU feature is disabled and the cache can grow without bound.
// The LRU feature performs best when maxsize is a power-of-two.
const DEFAULT_CACHE_SIZE: usize = usize::pow(2, 24);

const ENV_CACHE_SIZE: &str = "ZKWASM_MERKLE_CACHE_SIZE";

lazy_static::lazy_static! {
    pub static ref MERKLE_CACHE: Mutex<LruCache<(u64, [u8;  32]), Option<MerkleRecord>>> =
        Mutex::new(LruCache::<(u64, [u8;  32]), Option<MerkleRecord>>::new(
            NonZeroUsize::new(get_cache_size()).unwrap(),
        ));

    pub static ref DATA_CACHE: Mutex<LruCache<[u8; 32], Option<DataHashRecord>>> =
    Mutex::new(LruCache::<[u8; 32], Option<DataHashRecord>>::new(
        NonZeroUsize::new(get_cache_size()).unwrap(),
    ));
}

fn get_cache_size() -> usize {
    if let Ok(size_var) = std::env::var(ENV_CACHE_SIZE) {
        return size_var.parse::<usize>().unwrap_or(DEFAULT_CACHE_SIZE);
    }
    DEFAULT_CACHE_SIZE
}
