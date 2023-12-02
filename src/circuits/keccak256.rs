use crate::host::keccak256::{N_R, RATE_LANES, ROTATION_CONSTANTS, ROUND_CONSTANTS};
use crate::utils::field_to_u64;
use halo2_proofs::arithmetic::FieldExt;
use crate::circuits::{CommonGateConfig, Limb};
use halo2_proofs::{circuit::*, plonk::*};
use std::marker::PhantomData;
use crate::circuits::bits_arith::BitsArithChip;
use crate::circuits::bits_arith::BIT_XOR;
use crate::circuits::bits_arith::BIT_NOT_AND;

#[derive(Debug, Clone)]
pub struct KeccakState<F: FieldExt> {
    state: [[Limb<F>; 5]; 5],
    default: [[Limb<F>; 5]; 5],
    rc: [Limb<F>; N_R],
}

const HALF_DEBUG: bool = false;

pub struct KeccakChip<F: FieldExt> {
    pub config: CommonGateConfig,
    keccak_state: KeccakState<F>,
    round: u64,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakChip<F> {
    pub fn construct(config: CommonGateConfig) -> Self {
        let state = [[0u32; 5]; 5].map(|x| x.map(|_| Limb::new(None, F::zero())));
        let default = [[0u32; 5]; 5].map(|x| x.map(|_| Limb::new(None, F::zero())));
        let rc = ROUND_CONSTANTS.map(|x| Limb::new(None, F::from(x)));
        let state = KeccakState { state, default, rc };

        KeccakChip {
            round: 0,
            config,
            keccak_state: state,
            ///mapping rule: S[w(5y+x)+z] = state[x][y][z])]
            _marker: PhantomData,
        }
    }

    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.keccak_state.initialize(config, region, offset)
    }

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> CommonGateConfig {
        let bitsarithconfig = BitsArithChip::configure(cs);
        CommonGateConfig::configure(cs, &bitsarithconfig, shared_advice)
    }

    // assign the r as witness to call the permutation function and constrain the result to be the same as the digest
    pub fn get_permute_result(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
    ) -> Result<[Limb<F>; 4], Error> {
        let mut new_state = self.keccak_state.default.clone();
        for (x, (current_state, default)) in (self
            .keccak_state
            .state
            .iter()
            .zip(self.keccak_state.default.iter()))
        .enumerate()
        {
            for i in 0..5 {
                new_state[x][i] = self.config.select(
                    region,
                    &mut (),
                    offset,
                    &reset,
                    &current_state[i],
                    &default[i],
                    self.round,
                )?;
            }
        }

        println!("offset after pick state is {}", offset);

        //absorb
        let mut x = 0;
        let mut y = 0;

        for i in 0..RATE_LANES {
            new_state[x][y] = self.keccak_state.xor(
                &self.config,
                region,
                offset,
                &new_state[x][y],
                &values[i],
            )?;
            if x < 5 - 1 {
                x += 1;
            } else {
                y += 1;
                x = 0;
            }
        }

        println!("offset after xor state is {}", offset);

        self.keccak_state.state = new_state;

        self.keccak_state.permute(&self.config, region, offset)?;

        let part0 = self.keccak_state.state[0][0].value.clone();
        let part1 = self.keccak_state.state[1][0].value.clone();
        let part2 = self.keccak_state.state[2][0].value.clone();
        let part3 = self.keccak_state.state[3][0].value.clone();

        let part0_limb = Limb::new(None, part0);
        let part1_limb = Limb::new(None, part1);
        let part2_limb = Limb::new(None, part2);
        let part3_limb = Limb::new(None, part3);

        Ok([part0_limb, part1_limb, part2_limb, part3_limb])
    }

    pub(crate) fn assign_permute(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
        result: &[Limb<F>; 4],
    ) -> Result<(), Error> {
        println!("offset is {}", offset);
        let r = self.get_permute_result(region, offset, values, reset)?;
        for (r, result) in r.iter().zip(result.iter()) {
            assert_eq!(r.value, result.value);
            region.constrain_equal(
                result.cell.as_ref().unwrap().cell(),
                r.cell.as_ref().unwrap().cell(),
            )?;
        }

        println!("post offset is {}", offset);
        Ok(())
    }
}

impl<F: FieldExt> KeccakState<F> {
    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero = config.assign_constant(region, &mut (), offset, &F::zero())?;
        let state = [[0u32; 5]; 5].map(|x| x.map(|_| zero.clone()));
        let default = [[0u32; 5]; 5].map(|x| x.map(|_| zero.clone()));
        for i in 0..N_R {
            self.rc[i] = config.assign_constant(region, &mut (), offset, &self.rc[i].value)?;
        }
        Ok(())
    }

    // Combine for optimization opportunity, i.e. reduce decompose count
    pub fn xor_not_and(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        a: &Limb<F>,
        b: &Limb<F>,
        c: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        let d = (!field_to_u64(&b.value)) & field_to_u64(&c.value);
        let e = field_to_u64(&a.value) ^ d;
        let not_b_and_c = Limb::new(None, F::from(d));
        let res = Limb::new(None, F::from(e));
        let (_, a_limbs) = config.decompose_bytes(region, offset, a)?;
        let (_, b_limbs) = config.decompose_bytes(region, offset, b)?;
        let (_, c_limbs) = config.decompose_bytes(region, offset, c)?;
        let (_, f_limbs) = config.decompose_bytes(region, offset, &not_b_and_c)?;
        let (output, res_limbs) = config.decompose_bytes(region, offset, &res)?;

        for ((l, r), res) in b_limbs.zip(c_limbs).zip(f_limbs.clone()).into_iter() {
            config.assign_witness(
                region,
                &mut (),
                offset,
                [ Some(l), Some(r), Some(res), None, None, ],
                BIT_NOT_AND as u64,
            )?;
        }

        for ((l, r), res) in a_limbs.zip(f_limbs).zip(res_limbs).into_iter() {
            config.assign_witness(
                region,
                &mut (),
                offset,
                [ Some(l), Some(r), Some(res), None, None, ],
                BIT_XOR as u64,
            )?;
        }

        {
            let a = field_to_u64(&a.value);
            let b = field_to_u64(&b.value);
            let c = field_to_u64(&c.value);
            let res = a ^ ((!b) & c);
            assert_eq!(F::from(res), output.value);
        }
        Ok(output)
    }

    pub fn xor(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        let res = Limb::new(None, F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)));
        let (_, lhs_limbs) = config.decompose_bytes(region, offset, lhs)?;
        let (_, rhs_limbs) = config.decompose_bytes(region, offset, rhs)?;
        let (output, res_limbs) = config.decompose_bytes(region, offset, &res)?;

        for ((l, r), res) in lhs_limbs.zip(rhs_limbs).zip(res_limbs).into_iter() {
            config.assign_witness(
                region,
                &mut (),
                offset,
                [ Some(l), Some(r), Some(res), None, None, ],
                BIT_XOR as u64,
            )?;
        }
        Ok(output)
    }

    pub fn rotate_left(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        input: &Limb<F>,
        n: usize,
    ) -> Result<Limb<F>, Error> {
        let mut bit_limb = vec![];
        config.decompose_limb(region, &mut (), offset, &input, &mut bit_limb, 64)?;
        let mut bit_array_limb = Vec::with_capacity(64);

        for x in 0..64 {
            bit_array_limb.push(field_to_u64(&bit_limb[x].value));
        }

        bit_array_limb.rotate_left(n);

        let mut rotate_res_limb = Limb::new(None, F::zero());

        for (i, &bit) in bit_array_limb.iter().rev().enumerate() {
            rotate_res_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }

        let bit_limb1 = bit_limb[0..n].to_vec();
        let bit_limb2 = bit_limb[n..64].to_vec();

        let mut res_limb1 = Limb::new(None, F::zero());
        let mut res_limb2 = Limb::new(None, F::zero());

        for (i, bit) in bit_limb1.iter().rev().enumerate() {
            // little endian
            res_limb1.value += bit.value * F::from_u128(1 << i);
        }

        for (i, bit) in bit_limb2.iter().rev().enumerate() {
            res_limb2.value += bit.value * F::from_u128(1 << i);
        }

        // res_limb1.value + res_limb2.value * F::from_u128(1 << n) - rotate_res_limb.value = 0;
        let res = config.assign_line(
            region,
            &mut (),
            offset,
            [
                Some(res_limb1),
                Some(res_limb2),
                None,
                None,
                Some(rotate_res_limb),
                None,
            ],
            [
                Some(F::one()),
                Some(F::from_u128(1 << n)),
                None,
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?;

        Ok(res[2].clone())
    }

    pub fn theta(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let mut c = self.default[0].clone();

        let prev = |x| (x + 4) % 5;
        let next = |x| (x + 1) % 5;

        for x in 0..5 {
            let y = &self.state[x];
            let mut ci = y[0].clone();
            for i in 1..5 {
                ci = self.xor(config, region, offset, &ci, &y[i])?;
            }
            c[x] = ci;
        }

        for x in 0..5 {
            let di = self.rotate_left(config, region, offset, &c[next(x)], 1)?;
            let di = self.xor(config, region, offset, &c[prev(x)], &di)?;
            for y in 0..5 {
                self.state[x][y] = self.xor(config, region, offset, &self.state[x][y], &di)?;
            }
        }

        Ok(())
    }

    pub fn rho(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let mut out = self.default.clone();

        for x in 0..5 {
            for y in 0..5 {
                let rc = ROTATION_CONSTANTS[x][y];
                let rotate_limb = self.rotate_left(
                    config,
                    region,
                    offset,
                    &self.state[x][y],
                    rc.try_into().unwrap(),
                )?;
                out[x][y] = rotate_limb;
            }
        }

        self.state = out;

        Ok(())
    }

    pub fn pi(
        &mut self,
        _config: &CommonGateConfig,
        _region: &mut Region<F>,
        _offset: &mut usize,
    ) -> Result<(), Error> {
        let mut out = self.default.clone();

        for x in 0..5 {
            for y in 0..5 {
                out[y][(2 * x + 3 * y) % 5] = self.state[x][y].clone();
            }
        }

        self.state = out;
        Ok(())
    }

    pub fn xi(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let next = |x| (x + 1) % 5;
        let skip = |x| (x + 2) % 5;

        for x in 0..5 {
            for y in 0..5 {
                self.state[x][y] = self.xor_not_and(
                    config,
                    region,
                    offset,
                    &self.state[x][y],
                    &self.state[next(x)][y],
                    &self.state[skip(x)][y],
                )?;
            }
        }

        Ok(())
    }

    pub fn iota(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        round: usize,
    ) -> Result<(), Error> {
        self.state[0][0] = self.xor(config, region, offset, &self.state[0][0], &self.rc[round])?;
        Ok(())
    }

    pub fn round(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        round: usize,
    ) -> Result<(), Error> {
        self.theta(config, region, offset)?;
        self.rho(config, region, offset)?;
        self.pi(config, region, offset)?;
        self.xi(config, region, offset)?;
        self.iota(config, region, offset, round)?;

        Ok(())
    }

    pub fn permute(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        for round in 0..N_R {
            Self::round(self, config, region, offset, round)?;
        }

        Ok(())
    }
}
