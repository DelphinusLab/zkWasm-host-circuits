use halo2_proofs::pairing::bn256::Fr;
use crate::keccak;
use crate::keccak::Keccak;
use crate::utils::Limb;

/// The State is a 5x5 matrix of 64 bit lanes.
pub type State = [[Limb<Fr>; T]; T];

pub const BITRATE: usize = (1600 / LANE_SIZE) as usize;
pub const CAPACITY: usize = (512 / LANE_SIZE) as usize;
pub const L: usize = 6;
pub const RATE: usize = (1088 / LANE_SIZE) as usize;
pub const LANE_SIZE: u32 = 64;

/// The range of x and y coordinates for the sponge state.
pub const T: usize = 5;

/// The number of rounds for the 1600 bits permutation used in Keccak-256.
pub const N_R: usize = T * T - 1;

/// The number of next_inputs that are used inside the `absorb` circuit.
pub const RATE_LANES: usize = 17;

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

lazy_static::lazy_static! {
    pub static ref KECCAK_HASHER: keccak::Keccak<Fr, 5, 17> = Keccak::<Fr, 5, 17>::new();
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    #[test]
    fn test_keccak() {
        const ZERO_HASHER_SQUEEZE: &str =
            //force the hasher is for fr field result.
            "0x2f7053117e869a5a9d4035c2c93e2f902615e1f936995406bef3486ac90df1ec";
        let mut hasher = super::KECCAK_HASHER.clone();
        hasher.update(&[Fr::zero()]);
        let result = hasher.squeeze();

        println!("hash result is {:?}", result);
        assert_eq!(result.to_string(), ZERO_HASHER_SQUEEZE);
    }
}

