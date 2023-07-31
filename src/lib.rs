#![feature(array_zip)]
#![feature(slice_flatten)]
pub mod adaptor;
pub mod circuits;
pub mod host;
pub mod utils;
pub const MERKLE_DEPTH: usize = 32;
