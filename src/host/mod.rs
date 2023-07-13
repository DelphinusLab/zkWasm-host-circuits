pub mod bls;
pub mod bn256;
pub mod merkle;
pub mod rmd160;
pub mod kvpair;
pub mod poseidon;
pub mod jubjub;

use serde::{Deserialize, Serialize};
use halo2_proofs::arithmetic::FieldExt;

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct ExternalHostCallEntryTable(pub Vec<ExternalHostCallEntry>);

#[derive(Serialize, Deserialize, Debug)]
pub struct ExternalHostCallEntry {
    pub op: usize,
    pub value: u64,
    pub is_ret: bool,
}

#[derive(clap::ArgEnum, Clone, Copy, Debug)]
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
    KVPairSetRoot,   // 11
    KVPairGetRoot,   // 12
    KVPairAddress,   // 13
    KVPairSet,       // 14
    KVPairGet,       // 15
    SHA256New,
    SHA256Push,
    SHA256Finalize,
    PoseidonNew,
    PoseidonPush,
    PoseidonFinalize,
    JubjubSumNew,
    JubjubSumPush,
    JubjubSumResult,

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
                let mut acc = F::from_u128(v as u128);
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

    fn reset(&mut self) {
        match self {
            ReduceRule::Bytes(ref mut x, _) => {
                x.clear()
            }, // a * u64
            ReduceRule::Field(ref mut x, _shift) => {
                *x = F::zero()
            }, // 4 * u64
            ReduceRule::U64(ref mut x) => {
                *x = 0;
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
    pub fn total_len(&self) -> usize {
        self.rules.iter().fold(0, |acc, x| {
            acc + x.nb_inputs()
        })
    }
}

impl<F:FieldExt> Reduce<F> {
    /// take in a u64 value and update all the reduce rule accordingly
    pub fn reduce(&mut self, v: u64) {
        let mut cursor = self.cursor;
        let total = self.total_len();
        if cursor == 0 {
            for rule in self.rules.iter_mut() {
                rule.reset()
            }
        }
        for index in 0..self.rules.len() {
            if cursor >= self.rules[index].nb_inputs() {
                cursor = cursor - self.rules[index].nb_inputs();
            } else {
                self.rules[index].reduce(v, cursor);
                break
            }
        }
        self.cursor += 1;
        if self.cursor == total {
            self.cursor = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Reduce;
    use super::ReduceRule;
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::arithmetic::FieldExt;
    fn new_reduce(rules: Vec<ReduceRule<Fr>>) -> Reduce<Fr> {
        Reduce {
           cursor: 0,
           rules
        }
    }

    #[test]
    fn test_reduce_bytes() {
        let reducerule = ReduceRule::<Fr>::Bytes(vec![], 4);
        let mut reduce = Reduce { cursor:0, rules: vec![reducerule] };
        reduce.reduce(1);
    }

    #[test]
    fn test_reduce_bytes_twice() {
        let reducerule = ReduceRule::<Fr>::Bytes(vec![], 1);
        let mut reduce = Reduce { cursor:0, rules: vec![reducerule] };
        reduce.reduce(1);
        reduce.reduce(2);
        assert_eq!(reduce.rules[0].bytes_value().unwrap(), vec![2,0,0,0,0,0,0,0])
    }


    #[test]
    fn test_reduce_u64() {
        let mut get = new_reduce(vec![
                ReduceRule::U64(0),
                ReduceRule::U64(0),
                ReduceRule::U64(0),
                ReduceRule::U64(0),
            ]);
        get.reduce(12);
        assert_eq!(get.cursor, 1);
        assert_eq!(get.rules[0].u64_value().unwrap(), 12);
    }

    #[test]
    fn test_reduce_fr() {
        let mut get = new_reduce(vec![
                ReduceRule::Field(Fr::zero(), 64),
            ]);
        get.reduce(1);
        get.reduce(1);
        get.reduce(0);
        get.reduce(0);
        assert_eq!(get.rules[0].field_value().unwrap(), Fr::from_u128((1u128<<64)+1));
    }
}
