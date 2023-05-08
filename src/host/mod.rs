pub mod bls;
pub mod bn256;
pub mod merkle;
pub mod rmd160;
pub mod kvpair;

use serde::{Deserialize, Serialize};
use halo2_proofs::arithmetic::FieldExt;

#[derive(Serialize, Deserialize, Debug)]
pub struct ExternalHostCallEntryTable(pub Vec<ExternalHostCallEntry>);

#[derive(Serialize, Deserialize, Debug)]
pub struct ExternalHostCallEntry {
    pub op: usize,
    pub value: u64,
    pub is_ret: bool,
}

pub const MONGODB_URI:&str = "mongodb://localhost:27017";

pub enum ReduceRule<F: FieldExt> {
    Bytes(Vec<u8>, usize),
    Field(F, usize), // F * shiftbits
    USize(usize),
}

impl<F: FieldExt> ReduceRule<F> {
    fn nb_inputs(&self) -> usize {
        match self {
            ReduceRule::Bytes(_, a) => *a, // a * u64
            ReduceRule::Field(_, _) => 4, // 4 * u64
            ReduceRule::USize(_) => 4, // 4 * u64
        }
    }
    fn reduce(&mut self, _v: u64) {
        todo!();
    }
}

pub struct Reduce<F: FieldExt> {
    pub cursor: usize,
    pub rules: Vec<ReduceRule<F>>
}

impl<F:FieldExt> Reduce<F> {
    pub fn reduce(&mut self, v: u64) {
        let mut cursor = self.cursor;
        for index in 0..self.rules.len() {
           if cursor >= self.rules[index].nb_inputs() {
               cursor = cursor - self.rules[index].nb_inputs();
           } else {
               self.rules[index].reduce(v)
           }
        }
        self.cursor += 1;
    }
}
