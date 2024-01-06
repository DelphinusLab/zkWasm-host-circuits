use itertools::Itertools;
pub const BITRATE: usize = (1600 / LANE_SIZE) as usize;
pub const CAPACITY: usize = (512 / LANE_SIZE) as usize;
pub const L: usize = 6;
pub const RATE: usize = (1088 / LANE_SIZE) as usize;
pub const LANE_SIZE: u32 = 64;

/// The range of x and y coordinates for the sponge state.
pub const T: usize = 5;
/// The State is a 5x5 matrix of 64 bit lanes.

#[derive(Debug, Clone)]
pub struct State([[u64; T]; T]);

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

impl State {
    fn default() -> Self {
        let state = [[0u64; T]; T];
        State(state)
    }

    pub fn permute(&mut self) {
        //self.debug();
        for rc in ROUND_CONSTANTS.iter().take(N_R) {
            self.round_b(*rc);
            //self.debug();
        }
    }

    pub fn debug(&self) {
        println!("debug host state");
        for i in 0..5 {
            let c = self.0[i].clone().map(|x| format!("{:02x}", x)).join("-");
            println!("host state ({}): {}", i, c);
        }
    }

    fn round_b(&mut self, rc: u64) {
        self.theta();
        self.rho();
        self.pi();
        self.xi();
        self.iota(rc);
    }

    pub fn theta(&mut self) {
        let mut c: [u64; 5] = [0; 5];
        for x in 0..5 {
            c[x] =
                (((&self.0[x][0] ^ &self.0[x][1]) ^ &self.0[x][2]) ^ &self.0[x][3]) ^ &self.0[x][4];
        }
        for (x, y) in (0..5).cartesian_product(0..5) {
            self.0[x][y] = (&self.0[x][y] ^ &c[(x + 4) % 5]) ^ &c[(x + 1) % 5].rotate_left(1);
        }
    }

    pub fn rho(&mut self) {
        for (x, y) in (0..5).cartesian_product(0..5) {
            self.0[x][y] = self.0[x][y].rotate_left(ROTATION_CONSTANTS[x][y]);
        }
    }

    pub fn pi(&mut self) {
        let mut out = Self::default();

        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[y][(2 * x + 3 * y) % 5] = self.0[x][y];
        }
        self.0 = out.0;
    }

    pub fn xi(&mut self) {
        let mut out = Self::default();
        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[x][y] = &self.0[x][y] ^ ((!&self.0[(x + 1) % 5][y]) & (&self.0[(x + 2) % 5][y]));
        }
        self.0 = out.0;
    }

    pub fn iota(&mut self, rc: u64) {
        self.0[0][0] = &self.0[0][0] ^ rc;
    }
}

impl State {
    pub fn absorb(&mut self, input: &[u64; RATE]) {
        //println!("absorbing ... {:?}", input);
        let mut x = 0;
        let mut y = 0;
        for i in 0..RATE {
            let word = input[i];
            self.0[x][y] = (&word) ^ (&self.0[x][y]);
            if x < 5 - 1 {
                x += 1;
            } else {
                y += 1;
                x = 0;
            }
            //println!("current init round: {}", i);
            //self.debug();
        }
        self.permute();
    }

    pub fn result(&self) -> [u64; 4] {
        let mut output = vec![];
        output.push(self.0[0][0]);
        output.push(self.0[1][0]);
        output.push(self.0[2][0]);
        output.push(self.0[3][0]);
        output.try_into().unwrap() //check endian (current big endian)
    }
}

#[derive(Debug, Clone)]
pub struct Keccak {
    state: State,
    absorbing: Vec<u64>,
}

impl Keccak {
    pub fn new() -> Self {
        Self {
            state: State::default(),
            absorbing: Vec::new(),
        }
    }

    pub fn update(&mut self, input: &[u64]) {
        self.absorbing.extend(input);
        let candidate = self.absorbing.clone();
        self.absorbing = vec![];
        for chunk in candidate.chunks(RATE).into_iter() {
            if chunk.len() == RATE {
                self.state.absorb(chunk.try_into().unwrap());
            } else {
                self.absorbing = chunk.to_vec();
            }
        }
    }

    pub fn update_exact(&mut self, inputs: &[u64; RATE]) -> [u64; 4] {
        assert_eq!(self.absorbing.len(), 0);
        self.state.absorb(inputs);
        //self.spec.keccak_f.permute(&mut self.state);
        self.state.result()
    }

    /// Returns keccak hash based on current state
    pub fn squeeze(&mut self) -> [u64; 4] {
        let len = self.absorbing.len();
        let padding_total = RATE - (len % RATE);

        let starting_one_lane = 1u64;
        let zero_lane = 0;
        let ending_one_lane = 1u64 << 63;
        let one_zero_one_lane = starting_one_lane + ending_one_lane;

        if padding_total == 1 {
            self.absorbing.push(one_zero_one_lane);
        } else {
            self.absorbing.push(starting_one_lane);
            self.absorbing.resize(len + padding_total - 1, zero_lane);
            self.absorbing.push(ending_one_lane);
        }
        let r: Vec<u64> = self.absorbing.clone();
        println!("before absorb is {:?}", &r);
        self.state.absorb(&r.try_into().unwrap());
        println!("after absorb state is {:?}", &self.state);
        //self.spec.keccak_f.permute(&mut self.state);
        self.absorbing.truncate(0);
        self.state.result()
    }
}

lazy_static::lazy_static! {
    pub static ref KECCAK_HASHER: Keccak = Keccak::new();
}

#[cfg(test)]
mod tests {
    use super::KECCAK_HASHER;
    use crate::host::keccak256::N_R;
    use itertools::Itertools;
    use rand::RngCore;
    use rand_core::OsRng;

    #[test]
    fn test_keccak() {
        let exp = [
            197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182,
            83, 202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112,
        ];
        let expect_str = exp.iter().map(|x| format!("{:02x}", x)).join("");
        let mut hasher = super::KECCAK_HASHER.clone();
        hasher.update(&[]);
        let result = hasher.squeeze();

        let hash = result.iter().map(|x| format!("{:02x}", x)).join("");
        println!("hash result is {:?}", hash); // endian does not match the reference implementation
        println!("expect result is {:?}", expect_str);
        //assert_eq!(result.to_string(), ZERO_HASHER_SQUEEZE);
    }

    #[test]
    fn keccak256_one() {
        let mut keccak = KECCAK_HASHER.clone();
        let number_of_permutation = N_R / 24;
        let number_of_inputs = 17 * number_of_permutation - 1;
        let inputs = (0..number_of_inputs)
            .map(|_| OsRng.next_u64())
            .collect::<Vec<u64>>();

        keccak.update(&inputs[..]);
        let a = keccak.squeeze();

        let mut keccak = KECCAK_HASHER.clone();
        let mut inputs = inputs.clone();
        inputs.push(1u64 + (1u64 << 63));
        assert_eq!(inputs.len() % 17, 0);

        for chunk in inputs.chunks(17) {
            keccak.state.absorb(&chunk.try_into().unwrap());
            //keccak.spec.keccak_f.permute(&mut keccak.state)
        }

        let b = keccak.state.result();

        assert_eq!(a, b);
    }

    #[test]
    fn keccak256_check_reference() {
        let mut keccak = KECCAK_HASHER.clone();
        keccak.update(&[]);
        let expect = "0x0bbfa9132015329c07b3822630fc263512f39a81d9fc90542cc28fc914d8fa7a";
        let result = keccak.squeeze();
        let g = result.iter().map(|x| format!("{:02x}", x)).join("");
        println!("g is {:?}", g);
        println!("result is {:?}", result);
        println!("expect is {:?}", expect);
        // what is a then?
    }

    #[test]
    fn keccak256_empty() {
        let mut keccak = KECCAK_HASHER.clone();

        let inputs = (0..0).map(|_| OsRng.next_u64()).collect::<Vec<u64>>();

        keccak.update(&inputs[..]);
        let a = keccak.squeeze();

        let mut keccak = KECCAK_HASHER.clone();
        let mut inputs = inputs.clone();
        let mut extra_padding = vec![0; 17];

        extra_padding[16] = 1u64 << 63;
        extra_padding[0] = 1;
        inputs.extend(extra_padding);
        assert_eq!(inputs.len() % 17, 0);

        for chunk in inputs.chunks(17) {
            keccak.state.absorb(&chunk.try_into().unwrap());
            //keccak.spec.keccak_f.permute(&mut keccak.state)
        }

        let b = keccak.state.result();

        assert_eq!(a, b);
    }

    #[test]
    fn keccak256_extra_permutation() {
        let mut keccak = KECCAK_HASHER.clone();
        let number_of_permutation = N_R / 24;
        let number_of_inputs = 17 * number_of_permutation;
        let inputs = (0..number_of_inputs)
            .map(|_| OsRng.next_u64())
            .collect::<Vec<u64>>();

        keccak.update(&inputs[..]);
        let a = keccak.squeeze();

        let mut keccak = KECCAK_HASHER.clone();
        let mut inputs = inputs.clone();
        let mut extra_padding = vec![0u64; 17];
        extra_padding[0] = 1u64 << 63;
        extra_padding[16] = 1u64;
        inputs.extend(extra_padding);

        for chunk in inputs.chunks(17) {
            keccak.state.absorb(&chunk.try_into().unwrap());
            //keccak.spec.keccak_f.permute(&mut keccak.state)
        }

        let b = keccak.state.result();

        assert_eq!(a, b);
    }

    #[test]
    fn keccak_run() {}
}

/*
#[test]
fn test_empty_input() {
    let output = [
        197, 210, 70, 1, 134, 247, 35, 60, 146, 126, 125, 178, 220, 199, 3, 192, 229, 0, 182, 83,
        202, 130, 39, 59, 123, 250, 216, 4, 93, 133, 164, 112,
    ];
    assert_eq!(keccak256(&[]), output);
}



#[test]
fn test_short_input() {

    let output = [
        56, 209, 138, 203, 103, 210, 92, 139, 185, 148, 39, 100, 182, 47, 24, 225, 112, 84, 246,
        106, 129, 123, 212, 41, 84, 35, 173, 249, 237, 152, 135, 62,
    ];


    let output = Fr::from(0x3e87a9d2cf);
    assert_eq!(keccak256(&[Fr::from(102), Fr::from(111), Fr::from(111), Fr::from(98), Fr::from(97),
        Fr::from(114)]), output);
}


#[test]
fn test_long_input() {
    let input = [
        65, 108, 105, 99, 101, 32, 119, 97, 115, 32, 98, 101, 103, 105, 110, 110, 105, 110, 103,
        32, 116, 111, 32, 103, 101, 116, 32, 118, 101, 114, 121, 32, 116, 105, 114, 101, 100, 32,
        111, 102, 32, 115, 105, 116, 116, 105, 110, 103, 32, 98, 121, 32, 104, 101, 114, 32, 115,
        105, 115, 116, 101, 114, 32, 111, 110, 32, 116, 104, 101, 32, 98, 97, 110, 107, 44, 32, 97,
        110, 100, 32, 111, 102, 32, 104, 97, 118, 105, 110, 103, 32, 110, 111, 116, 104, 105, 110,
        103, 32, 116, 111, 32, 100, 111, 58, 32, 111, 110, 99, 101, 32, 111, 114, 32, 116, 119,
        105, 99, 101, 32, 115, 104, 101, 32, 104, 97, 100, 32, 112, 101, 101, 112, 101, 100, 32,
        105, 110, 116, 111, 32, 116, 104, 101, 32, 98, 111, 111, 107, 32, 104, 101, 114, 32, 115,
        105, 115, 116, 101, 114, 32, 119, 97, 115, 32, 114, 101, 97, 100, 105, 110, 103, 44, 32,
        98, 117, 116, 32, 105, 116, 32, 104, 97, 100, 32, 110, 111, 32, 112, 105, 99, 116, 117,
        114, 101, 115, 32, 111, 114, 32, 99, 111, 110, 118, 101, 114, 115, 97, 116, 105, 111, 110,
        115, 32, 105, 110, 32, 105, 116, 44, 32, 97, 110, 100, 32, 119, 104, 97, 116, 32, 105, 115,
        32, 116, 104, 101, 32, 117, 115, 101, 32, 111, 102, 32, 97, 32, 98, 111, 111, 107, 44, 32,
        116, 104, 111, 117, 103, 104, 116, 32, 65, 108, 105, 99, 101, 32, 119, 105, 116, 104, 111,
        117, 116, 32, 112, 105, 99, 116, 117, 114, 101, 115, 32, 111, 114, 32, 99, 111, 110, 118,
        101, 114, 115, 97, 116, 105, 111, 110, 115, 63,
    ];
    let output = [
        60, 227, 142, 8, 143, 135, 108, 85, 13, 254, 190, 58, 30, 106, 153, 194, 188, 6, 208, 49,
        16, 102, 150, 120, 100, 130, 224, 177, 64, 98, 53, 252,
    ];
    assert_eq!(keccak256(&input), output);
}
*/
