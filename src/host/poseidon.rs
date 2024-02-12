use halo2_proofs::pairing::bn256::Fr;
use poseidon::Poseidon;
use poseidon::Spec;

pub const PREFIX_CHALLENGE: u64 = 0u64;
pub const PREFIX_POINT: u64 = 1u64;
pub const PREFIX_SCALAR: u64 = 2u64;

// We have two hasher here
// 1. MERKLE_HASHER that is used for non sponge hash for hash two merkle siblings
// 2. POSEIDON_HASHER thas is use for poseidon hash of data
lazy_static::lazy_static! {
    pub static ref POSEIDON_HASHER: poseidon::Poseidon<Fr, 9, 8> = Poseidon::<Fr, 9, 8>::new(8, 63);
    pub static ref MERKLE_HASHER: poseidon::Poseidon<Fr, 3, 2> = Poseidon::<Fr, 3, 2>::new(8, 57);
    pub static ref MERKLE_LEAF_HASHER: poseidon::Poseidon<Fr, 3, 2> = Poseidon::<Fr, 3, 2>::new(8, 57);
    pub static ref POSEIDON_HASHER_SPEC: poseidon::Spec<Fr, 9, 8> = Spec::new(8, 63);
    pub static ref MERKLE_HASHER_SPEC: poseidon::Spec<Fr, 3, 2> = Spec::new(8, 57);
    pub static ref MERKLE_LEAF_HASHER_SPEC: poseidon::Spec<Fr, 3, 2> = Spec::new(8, 57);
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    #[test]
    fn test_poseidon() {
        const ZERO_HASHER_SQUEEZE: &str =
            "0x03f943aabd67cd7b72a539f3de686c3280c36c572be09f2b9193f5ef78761c6b"; //force the hasher is for fr field result.
        let mut hasher = super::POSEIDON_HASHER.clone();
        hasher.update(&[Fr::zero()]);
        let result = hasher.squeeze();
        println!("hash result is {:?}", result);
        assert_eq!(result.to_string(), ZERO_HASHER_SQUEEZE);
    }
}
