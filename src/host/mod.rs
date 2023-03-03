pub mod merkle;
pub mod bls;

use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct ExternalHostCallEntryTable(pub Vec<ExternalHostCallEntry>);

#[derive(Serialize, Deserialize, Debug)]
pub struct ExternalHostCallEntry {
    pub op: usize,
    pub value: u64,
    pub is_ret: bool,
}
