use poseidon::Poseidon;
use halo2_proofs::pairing::bn256::Fr;

pub const T: usize = 9;
pub const RATE: usize = 8;
pub const R_F: usize = 8;
pub const R_P: usize = 63;

pub const PREFIX_CHALLENGE: u64 = 0u64;
pub const PREFIX_POINT: u64 = 1u64;
pub const PREFIX_SCALAR: u64 = 2u64;

pub fn gen_hasher() -> Poseidon<Fr, T, RATE> {
   Poseidon::<Fr, T, RATE>::new(R_F, R_P)
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    #[test]
    fn test_poseidon() {
        let mut hasher = super::gen_hasher();
        hasher.update(&[Fr::zero()]);
        println!("hash result is {:?}", hasher.squeeze());
    }
}
