use poseidon::Poseidon;
use halo2_proofs::pairing::bn256::Fq;

pub const T: usize = 9;
pub const RATE: usize = 8;
pub const R_F: usize = 8;
pub const R_P: usize = 63;

pub const PREFIX_CHALLENGE: u64 = 0u64;
pub const PREFIX_POINT: u64 = 1u64;
pub const PREFIX_SCALAR: u64 = 2u64;

pub fn gen_hasher() -> Poseidon<Fq, T, RATE> {
   Poseidon::<Fq, T, RATE>::new(R_F, R_P)
}


