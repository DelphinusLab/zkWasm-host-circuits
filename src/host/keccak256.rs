use halo2_proofs::pairing::bn256::Fr;

use crate::utils::Limb;

/// The State is a 5x5 matrix of 64 bit lanes.
pub type State = [[Limb<Fr>; T]; T];

pub const b: usize = 1600;
pub const c: usize = 512;
pub const l: usize = 6;
pub const RATE: usize = 1088;
pub const LANE_SIZE: u32 = 64;

/// The range of x and y coordinates for the sponge state.
pub const T: usize = 5;

/// The number of rounds for the 1600 bits permutation used in Keccak-256.
pub const N_R: usize = 24;

/// The number of next_inputs that are used inside the `absorb` circuit.
pub const NEXT_INPUTS_LANES: usize = 17;

/// The Keccak [round constants](https://github.com/Legrandin/pycryptodome/blob/016252bde04456614b68d4e4e8798bc124d91e7a/src/keccak.c#L257-L282)
pub static ROUND_CONSTANTS: [u64; N_R] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// The Keccak [rotation offsets](https://github.com/Legrandin/pycryptodome/blob/016252bde04456614b68d4e4e8798bc124d91e7a/src/keccak.c#L232-L255)
pub static ROTATION_CONSTANTS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/* 
#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    #[test]
    fn test_keccak() {
        const ZERO_HASHER_SQUEEZE: &str =
            "044852b2a670ade5407e78fb2863c51de9fcb96542a07186fe3aeda6bb8a116d"; //force the hasher is for fr field result.
        //let mut hasher = super::keccak_hash;
        //hasher.update(&[Fr::zero()]);
        //let result = hasher.squeeze();
        let result = web3::signing::keccak256(&[0u8]);
        println!("hash result is {:?}", result);
        assert_eq!(from_utf8(result), ZERO_HASHER_SQUEEZE);
    }
}
*/