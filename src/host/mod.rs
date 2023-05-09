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

pub enum ForeignInst {
    Log = 0,
    BlspairG1,
    BlspairG2,
    BlspairG3,
    BlsSumG1,
    BlsSumResult,
    Bn254SumG1,
    Bn254SumResult,
    Bn254PairG1,
    Bn254PairG2,
    Bn254PairG3,
    KVPairSetRoot,
    KVPairGetRoot,
    KVPairSet,
    KVPairGet,
}

pub const MONGODB_URI:&str = "mongodb://localhost:27017";

pub enum ReduceRule<F: FieldExt> {
    Bytes(Vec<u8>, usize),
    Field(F, usize), // F * shiftbits
    U64(u64),
}

impl<F: FieldExt> ReduceRule<F> {
    fn nb_inputs(&self) -> usize {
        match self {
            ReduceRule::Bytes(_, a) => *a, // a * u64
            ReduceRule::Field(_, _) => 4, // 4 * u64
            ReduceRule::U64(_) => 1, // 4 * u64
        }
    }
    fn reduce(&mut self, v: u64, offset: usize) {
        match self {
            ReduceRule::Bytes(ref mut x, _) => {
                let mut bytes: Vec<u8> = v.to_le_bytes().to_vec();
                x.append(&mut bytes);
            }, // a * u64
            ReduceRule::Field(ref mut x, shift) => {
                let mut acc = F::one();
                for _ in 0..offset {
                    acc = acc * F::from_u128(1u128 << *shift)
                }
                *x = *x + acc
            }, // 4 * u64
            ReduceRule::U64(ref mut x) => {
                *x = v;
            }, // 1 * u64
        }
    }

    pub fn field_value(&self) -> Option<F> {
        match self {
            ReduceRule::Bytes(_, _) => None,
            ReduceRule::Field(f, _) => Some(*f), // 4 * u64
            ReduceRule::U64(_) => None, // 4 * u64
        }
    }
    pub fn bytes_value(&self) -> Option<Vec<u8>> {
        match self {
            ReduceRule::Bytes(b, _) => Some(b.clone()),
            ReduceRule::Field(_, _) => None, // 4 * u64
            ReduceRule::U64(_) => None, // 4 * u64
        }
    }
    pub fn u64_value(&self) -> Option<u64> {
        match self {
            ReduceRule::Bytes(_, _) => None,
            ReduceRule::Field(_, _) => None, // 4 * u64
            ReduceRule::U64(v) => Some(*v), // 4 * u64
        }
    }
}

pub struct Reduce<F: FieldExt> {
    pub cursor: usize,
    pub rules: Vec<ReduceRule<F>>
}

impl<F: FieldExt> Reduce<F> {
    pub fn new(rules: Vec<ReduceRule<F>>) -> Self {
        Reduce {
            cursor:0,
            rules,
        }
    }
}

impl<F:FieldExt> Reduce<F> {
    pub fn reduce(&mut self, v: u64) {
        let mut cursor = self.cursor;
        let mut total = 0;
        for index in 0..self.rules.len() {
            total += self.rules[index].nb_inputs(); 
            if cursor >= self.rules[index].nb_inputs() {
                cursor = cursor - self.rules[index].nb_inputs();
            } else {
                self.rules[index].reduce(v, cursor);
                break
            }
        }
        self.cursor += 1;
        // Reset to 0 if cursor points to the end of the reducer
        if self.cursor == total {
            self.cursor = 0;
        }
    }
}
