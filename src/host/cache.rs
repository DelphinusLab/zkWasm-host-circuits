use crate::host::kvpair::MerkleRecord;
use lru::LruCache;
use std::num::NonZeroUsize;
use std::sync::Mutex;
use once_cell::sync::Lazy;
use std::env;

// Use OneCell: https://docs.rs/once_cell/1.4.0/once_cell/ so we can init the Cache size and Preloading in future.

// If maxsize is set to None, the LRU feature is disabled and the cache can grow without bound.
// The LRU feature performs best when maxsize is a power-of-two.
pub const DEFAULT_CACHE_SIZE: usize = usize::pow(2, 17);
pub const CACHE_SIZE_KEY: &str = "MERKLE_CACHE_SIZE";

pub fn get_cache_key(cname: String, index: u32, hash: &[u8; 32]) -> String {
    cname + &index.to_string() + &hex::encode(hash)
}

pub static MERKLE_CACHE: Lazy<Mutex<LruCache<String, MerkleRecord>>> = Lazy::new ( || {
    let merkle_cache_size = match env::var(CACHE_SIZE_KEY) {
        Ok(v) => { let size:usize = v.parse().unwrap(); size},
        Err(_) => { DEFAULT_CACHE_SIZE },
    };
    println!("initializing MERKLE_CACHE with cap: {:?}", merkle_cache_size);

    Mutex::new(LruCache::<String, MerkleRecord>::new(
        NonZeroUsize::new(merkle_cache_size).unwrap()))
});
