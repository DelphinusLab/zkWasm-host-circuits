use std::marker::PhantomData;
use crate::common::*;
use itertools::Itertools;
use halo2_proofs::arithmetic::FieldExt;
use crate::utils::field_to_u64;
#[derive(Debug, Clone, PartialEq)]
pub struct State<F: FieldExt, const T: usize>(pub(crate) [[F; T];T]);

impl<F: FieldExt, const T: usize> Default for State<F, T> {
    fn default() -> Self {
        let state = [[F::zero(); T];T];
        State(state)
    }
}

#[derive(Debug, Clone)]
pub struct Keccak<F: FieldExt, const T: usize, const RATE: usize> {
    state: State<F,T>,
    spec: Spec<F, T, RATE>,
    absorbing: Vec<F>,
}

impl<F: FieldExt, const T: usize, const RATE: usize> Keccak<F, T, RATE> {
    pub fn new() -> Self {
        let security_level = (1088, 512);

        Self {
            state: State::default(),
            // rate & capacity in u64
            spec: Spec::new(RATE, security_level.1 / 64),
            absorbing: Vec::new(),
        }
    }
}

impl<F: FieldExt, const T: usize, const RATE: usize > Keccak<F, T, RATE> {
    /*
    pub fn update(&mut self, input: &[F]) {

        // offset for `input`
        let mut offset = 0;

        let absorbing_len = self.absorbing.len();
        if absorbing_len > 0 && absorbing_len + input.len() >= RATE {
            // concat absorbing and input up to the next full `rate`
            offset = RATE - absorbing_len;
            self.absorbing.extend(&input[0..offset]);
            self.spec.absorb(&mut self.state, &self.absorbing);
            self.absorbing.truncate(0);
        }

        let chunks_total = (input.len() - offset) / RATE;
        if chunks_total != 0 {
            // absorb all chunks
            let tail = offset + (RATE * chunks_total);
            self.spec.absorb(&mut self.state, &input[offset..tail]);
            offset = tail;
        }

        if offset != input.len() {
            // save the remainder
            self.absorbing.extend(&input[offset..]);
        }
    }
    */
    pub fn update(&mut self, input: &[F]) {
        // offset for `input`
        let mut input_elements = self.absorbing.clone();
        input_elements.extend_from_slice(input);

        for chunk in input_elements.chunks(RATE) {
            if chunk.len() < RATE {
                // Must be the last iteration of this update. Feed unpermutaed inputs to the
                // absorbation line
                self.absorbing = chunk.to_vec();
            } else {
                // Add new chunk of inputs for the next permutation cycle.
                self.spec.absorb(&mut self.state, chunk);
                // Perform intermediate permutation
                self.spec.keccak_f.permute(&mut self.state);
                // Flush the absorption line
                self.absorbing.clear();
            }
        }
    }

    pub fn update_exact(&mut self, inputs: &[F; RATE]) -> F {
        assert_eq!(self.absorbing.len(), 0);

        self.spec.absorb(&mut self.state, inputs);
        self.spec.keccak_f.permute(&mut self.state);
        self.spec.result(&mut self.state)
    }

    /// Returns keccak hash based on current state
    pub fn squeeze(&mut self) -> F {
        let len = self.absorbing.len();
        let padding_total = RATE - (len % RATE);

        let starting_one_lane = F::from_u128(1u128 << 63);
        let zero_lane = F::zero();
        let ending_one_lane = F::from(1);
        let one_zero_one_lane = starting_one_lane + ending_one_lane;

        if padding_total == 1 {
            self.absorbing.push(one_zero_one_lane);
        } else {
            self.absorbing.push(starting_one_lane);
            self.absorbing.resize(len + padding_total - 1, zero_lane);
            self.absorbing.push(ending_one_lane);
        }
        self.spec.absorb(&mut self.state, &self.absorbing);
        self.spec.keccak_f.permute(&mut self.state);
        self.absorbing.truncate(0);
        self.spec.result(&mut self.state)
    }

}

#[derive(Default, Clone,Debug)]
pub struct KeccakF<F: FieldExt, const T: usize, const RATE: usize> {
    _marker: PhantomData<F>
}

impl<F: FieldExt, const T: usize, const RATE: usize> KeccakF<F, T, RATE> {
    pub fn permute(&self, a: &mut State<F,T>) {
        for rc in ROUND_CONSTANTS.iter().take(PERMUTATION) {
            *a = KeccakF::<F,T,RATE>::round_b(a.clone(), *rc);
        }
    }

    fn round_b(a: State<F, T>, rc: u64) -> State<F, T> {
        let s1 = KeccakF::<F, T, RATE>::theta(a);
        let s2 = KeccakF::<F, T, RATE>::rho(s1);
        let s3 = KeccakF::<F, T, RATE>::pi(s2);
        let s4 = KeccakF::<F, T, RATE>::xi(s3);
        KeccakF::<F, T, RATE>::iota(s4, rc)
    }

    pub fn theta(a: State<F, T>) -> State<F, T> {
        let mut c: [F; 5] = [F::zero(); 5];
        let mut out: State<F, T> = State::default();

        for x in 0..5 {
            c[x] = F::from(field_to_u64(&a.0[x][0]) ^ field_to_u64(&a.0[x][1]) ^ field_to_u64(&a.0[x][2]) ^
                               field_to_u64(&a.0[x][3]) ^ field_to_u64(&a.0[x][4]));
        }

        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[x][y] = F::from(field_to_u64(&a.0[x][y]) ^ field_to_u64(&c[(x + 4) % 5])
                                    ^ field_to_u64(&c[(x + 1) % 5]).rotate_left(1));
        }
        out
    }

    pub fn rho(a: State<F, T>) -> State<F, T> {
        let mut out: State<F, T> = State::default();
        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[x][y] = F::from(field_to_u64(&a.0[x][y]).rotate_left(ROTATION_CONSTANTS[x][y]));
        }
        out
    }

    pub fn pi(a: State<F, T>) -> State<F, T> {
        let mut out: State<F, T> = State::default();

        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[y][(2 * x + 3 * y) % 5] = a.0[x][y];
        }
        out
    }

    pub fn xi(a: State<F, T>) -> State<F, T> {
        let mut out: State<F, T> = State::default();
        for (x, y) in (0..5).cartesian_product(0..5) {
            out.0[x][y] = F::from(field_to_u64(&a.0[x][y]) ^ (!field_to_u64(&a.0[(x + 1) % 5][y]) & field_to_u64(&a.0[(x + 2) % 5][y])));
        }
        out
    }

    pub fn iota(a: State<F, T>, rc: u64) -> State<F, T> {
        let mut out = a;
        out.0[0][0] = F::from(field_to_u64(&out.0[0][0]) ^ rc);
        out
    }
}
#[derive(Debug, Clone)]
pub struct Spec<F: FieldExt, const T: usize, const RATE: usize> {
    rate: usize,
    capacity: usize,
    keccak_f: KeccakF<F, T, RATE>,
}

impl<F: FieldExt, const T: usize, const RATE: usize> Spec<F,T,RATE> {
    pub fn new(rate: usize, capacity: usize) -> Spec<F,T,RATE> {
        Spec {
            rate,
            capacity,
            keccak_f: KeccakF::default(),
        }
    }

    pub fn absorb(&self, state: &mut State<F, T>, input: &[F]) {

        debug_assert_eq!(input.len() % RATE, 0);

        let mut x = 0;
        let mut y = 0;
        for i in 0..RATE {
            let word = input[i];
            state.0[x][y] = F::from(field_to_u64(&word) ^ field_to_u64(&state.0[x][y]));
            if x < 5 - 1 {
                x += 1;
            } else {
                y += 1;
                x = 0;
            }
        }

    }

    pub fn result(&self, state: &mut State<F, T>) -> F {
        let mut output = vec![];
        output.push(state.0[0][0]);
        output.push(state.0[0][1]);
        output.push(state.0[0][2]);
        output.push(state.0[0][3]);

        let result = ((output[0] * F::from_u128(1u128 << 64) + output[1])
            * F::from_u128(1u128 << 64) + output[2])
            * F::from_u128(1u128 << 64) + output[3];
        result
    }
}

//#[cfg(test)]
use halo2_proofs::pairing::bn256::Fr;

fn keccak256(msg: &[Fr]) -> Fr {
    let mut keccak:Keccak<Fr, 5, 17>= Keccak::<Fr, 5, 17>::new();
    keccak.update(msg);
    let a = keccak.squeeze();

    let mut keccak:Keccak<Fr, 5, 17>= Keccak::<Fr, 5, 17>::new();
    for byte in msg {
        keccak.update(&[*byte]);
    }
    let b = keccak.squeeze();

    assert_eq!(a, b);

    a
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

 */

#[test]
fn test_short_input() {

    /*let output = [
        56, 209, 138, 203, 103, 210, 92, 139, 185, 148, 39, 100, 182, 47, 24, 225, 112, 84, 246,
        106, 129, 123, 212, 41, 84, 35, 173, 249, 237, 152, 135, 62,
    ];

     */
    let output = Fr::from(0x3e87a9d2cf);
    assert_eq!(keccak256(&[Fr::from(102), Fr::from(111), Fr::from(111), Fr::from(98), Fr::from(97),
        Fr::from(114)]), output);
}

/*
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