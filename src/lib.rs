#![feature(slice_flatten)]

pub mod adaptor;
pub mod circuits;
pub mod host;
pub mod proof;
pub mod utils;

pub extern crate anyhow;
pub const DEFAULT_CIRCUITS_K: u32 = 22;
