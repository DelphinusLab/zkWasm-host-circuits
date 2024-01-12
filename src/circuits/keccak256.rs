use crate::circuits::bits_arith::BitsArithChip;
use crate::circuits::bits_arith::BitsArithConfig;
use crate::circuits::bits_arith::BIT_NOT_AND;
use crate::circuits::bits_arith::BIT_ROTATE_LEFT;
use crate::circuits::bits_arith::BIT_XOR;
use crate::circuits::{CommonGateConfig, Limb};
use crate::host::keccak256::{N_R, RATE_LANES, ROTATION_CONSTANTS, ROUND_CONSTANTS};

use crate::utils::field_to_u64;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::{circuit::*, plonk::*};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct KeccakState<F: FieldExt> {
    state: [[Limb<F>; 5]; 5],
    default: [[Limb<F>; 5]; 5],
    rc: [Limb<F>; N_R],
}

#[derive(Debug, Clone)]
pub struct KeccakGateConfig {
    pub common: CommonGateConfig,
    pub arith: BitsArithConfig,
}

pub struct KeccakChip<F: FieldExt> {
    pub config: KeccakGateConfig,
    keccak_state: KeccakState<F>,
    round: u64,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakChip<F> {
    pub fn construct(config: KeccakGateConfig) -> Self {
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
        config: &KeccakGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let mut bitschip = BitsArithChip::new(self.config.arith.clone());
        bitschip.initialize(region, &mut 1)?;
        self.keccak_state.initialize(&config.common, region, offset)
    }

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> KeccakGateConfig {
        let bitsarithconfig = BitsArithChip::configure(cs);
        KeccakGateConfig {
            arith: bitsarithconfig.clone(),
            common: CommonGateConfig::configure(cs, &bitsarithconfig, shared_advice),
        }
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
                new_state[x][i] = self.config.common.select(
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

        //absorb
        let mut x = 0;
        let mut y = 0;

        for i in 0..RATE_LANES {
            new_state[x][y] = self.keccak_state.xor(
                &self.config.common,
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

        self.keccak_state.state = new_state;

        self.keccak_state
            .permute(&self.config.common, region, offset)?;

        let part0 = self.keccak_state.state[0][0].clone();
        let part1 = self.keccak_state.state[1][0].clone();
        let part2 = self.keccak_state.state[2][0].clone();
        let part3 = self.keccak_state.state[3][0].clone();

        Ok([part0, part1, part2, part3])
    }

    pub(crate) fn assign_permute(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
        result: &[Limb<F>; 4],
    ) -> Result<(), Error> {
        let r = self.get_permute_result(region, offset, values, reset)?;
        for (r, result) in r.iter().zip(result.iter()) {
            assert_eq!(r.value, result.value);
            region.constrain_equal(
                result.cell.as_ref().unwrap().cell(),
                r.cell.as_ref().unwrap().cell(),
            )?;
        }
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
        self.state = [[0u32; 5]; 5].map(|x| x.map(|_| zero.clone()));
        self.default = [[0u32; 5]; 5].map(|x| x.map(|_| zero.clone()));
        for i in 0..N_R {
            self.rc[i] = config.assign_constant(region, &mut (), offset, &self.rc[i].value)?;
        }
        Ok(())
    }

    pub fn debug(&mut self) {
        println!("debug state");
        for i in 0..5 {
            let c = self.state[i]
                .clone()
                .map(|x| format!("{:02x}", field_to_u64(&x.value)))
                .join("-");
            println!("state({}): {}", i, c);
        }
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
        let res = Limb::new(None, F::from(e)); // reference
        config.decompose_bytes(region, offset, b, 0, BIT_NOT_AND as u64)?;
        config.decompose_bytes(region, offset, c, 0, 0)?;
        config.decompose_bytes(region, offset, &not_b_and_c, 0, BIT_XOR as u64)?;
        config.decompose_bytes(region, offset, a, 0, 0)?;
        let (output, _) = config.decompose_bytes(region, offset, &res, 0, 0)?;

        {
            let a = field_to_u64(&a.value);
            let b = field_to_u64(&b.value);
            let c = field_to_u64(&c.value);
            let res = a ^ ((!b) & c);
            assert_eq!(F::from(res), output.value);
        }
        Ok(output)
    }

    pub fn xor_not_and_ext(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        a: &Limb<F>,
        b: &Limb<F>,
        c: &Limb<F>,
        last_op: u64,
    ) -> Result<Limb<F>, Error> {
        let d = (!field_to_u64(&b.value)) & field_to_u64(&c.value);
        let e = field_to_u64(&a.value) ^ d;
        let not_b_and_c = Limb::new(None, F::from(d));
        let res = Limb::new(None, F::from(e)); // reference
        config.decompose_bytes(region, offset, c, 0, 0)?;
        config.decompose_bytes(region, offset, &not_b_and_c, 0, BIT_XOR as u64)?;
        config.decompose_bytes(region, offset, a, 0, 0)?;
        let (output, _) = config.decompose_bytes(region, offset, &res, 0, last_op)?;

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
        let res = Limb::new(
            None,
            F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)),
        );
        let (_, b1) = config.decompose_bytes(region, offset, lhs, 0, BIT_XOR as u64)?; // start of the lookup line
        let (_, b2) = config.decompose_bytes(region, offset, rhs, 0, 0)?;
        let (output, b3) = config.decompose_bytes(region, offset, &res, 0, 0)?;
        assert_eq!(
            field_to_u64(&b2[0].value) ^ field_to_u64(&b1[0].value),
            field_to_u64(&b3[0].value)
        );
        Ok(output)
    }

    pub fn xor_cont(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
        last_op: u64,
    ) -> Result<Limb<F>, Error> {
        let res = Limb::new(
            None,
            F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)),
        );
        let (_, b1) = config.decompose_bytes(region, offset, lhs, 0, BIT_XOR as u64)?; // start of the lookup line
        let (_, b2) = config.decompose_bytes(region, offset, rhs, 0, 0)?;
        let (output, b3) = config.decompose_bytes(region, offset, &res, 0, last_op)?;
        assert_eq!(
            field_to_u64(&b2[0].value) ^ field_to_u64(&b1[0].value),
            field_to_u64(&b3[0].value)
        );
        Ok(output)
    }

    pub fn xor_ext(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
        last_op: u64,
    ) -> Result<Limb<F>, Error> {
        let res = Limb::new(
            None,
            F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)),
        );

        config.decompose_bytes(region, offset, rhs, 0, 0)?;
        let (output, _) = config.decompose_bytes(region, offset, &res, 0, last_op)?;

        assert_eq!(
            field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value),
            field_to_u64(&output.value)
        );

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
        let v = field_to_u64(&input.value).rotate_left(n as u32);
        let chunk = n / 8; // how many chunks we have to move
        let rem = n % 8; // how many bits we have to move
        let (_, bytes) = config.decompose_bytes(
            region,
            offset,
            input,
            chunk,
            (BIT_ROTATE_LEFT as usize + rem) as u64,
        )?;
        config.assign_witness(
            region,
            &mut (),
            offset,
            [
                Some(bytes[7].clone()),
                Some(bytes[0].clone()),
                Some(bytes[1].clone()),
                Some(bytes[2].clone()),
                None,
            ],
            0,
        )?;
        config.assign_witness(
            region,
            &mut (),
            offset,
            [
                Some(bytes[3].clone()),
                Some(bytes[4].clone()),
                Some(bytes[5].clone()),
                Some(bytes[6].clone()),
                None,
            ],
            0,
        )?;
        let (v, bs) = config.decompose_bytes(region, offset, &Limb::new(None, F::from(v)), 0, 0)?;
        for i in 0..7 {
            let op1 = field_to_u64(&bytes[i].value);
            let op2 = field_to_u64(&bytes[(i + 7) % 8].value);
            let op3 = field_to_u64(&bs[i].value);
            if rem == 0 {
                assert_eq!(op1, op3);
            } else {
                assert_eq!(((op1 << rem) & 0xff) + (op2 >> (8 - rem)), op3);
            }
        }
        Ok(v)
    }

    pub fn rotate_left_cont(
        &self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        input: &Limb<F>,
        n: usize,
        last_op: u64,
    ) -> Result<Limb<F>, Error> {
        let v = field_to_u64(&input.value).rotate_left(n as u32);
        let chunk = n / 8; // how many chunks we have to move
        let rem = n % 8; // how many bits we have to move
        let (_, bytes) = config.decompose_bytes(
            region,
            offset,
            input,
            chunk,
            (BIT_ROTATE_LEFT as usize + rem) as u64,
        )?;
        config.assign_witness(
            region,
            &mut (),
            offset,
            [
                Some(bytes[7].clone()),
                Some(bytes[0].clone()),
                Some(bytes[1].clone()),
                Some(bytes[2].clone()),
                None,
            ],
            0,
        )?;
        config.assign_witness(
            region,
            &mut (),
            offset,
            [
                Some(bytes[3].clone()),
                Some(bytes[4].clone()),
                Some(bytes[5].clone()),
                Some(bytes[6].clone()),
                None,
            ],
            0,
        )?;
        let (v, bs) = config.decompose_bytes(region, offset, &Limb::new(None, F::from(v)), 0, last_op)?;
        for i in 0..7 {
            let op1 = field_to_u64(&bytes[i].value);
            let op2 = field_to_u64(&bytes[(i + 7) % 8].value);
            let op3 = field_to_u64(&bs[i].value);
            if rem == 0 {
                assert_eq!(op1, op3);
            } else {
                assert_eq!(((op1 << rem) & 0xff) + (op2 >> (8 - rem)), op3);
            }
        }
        Ok(v)
    }

    pub fn iota_theta(
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
            for i in 1..4 {
                ci = self.xor_ext(config, region, offset, &ci, &y[i],BIT_XOR as u64)?;
            }
            ci = self.xor_ext(config, region, offset, &ci, &y[4],0)?;
            c[x] = ci;
        }

        for x in 0..5 {
            let di = self.rotate_left_cont(config, region, offset, &c[next(x)], 1,BIT_XOR as u64)?;
            let di = self.xor_ext(config, region, offset, &di,&c[prev(x)], BIT_XOR as u64)?;
            self.state[x][0] = self.xor_ext(config, region, offset, &di, &self.state[x][0],0)?;
            for y in 1..5 {
                // TODO: d[x] is the same for the whole y loop, consider reuse d[x]
                self.state[x][y] = self.xor(config, region, offset, &self.state[x][y], &di)?;
            }
        }

        Ok(())
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
            ci = self.xor_cont(config, region, offset, &ci, &y[1],BIT_XOR as u64)?;
            for i in 2..4 {
                ci = self.xor_ext(config, region, offset, &ci, &y[i],BIT_XOR as u64)?;
            }
            ci = self.xor_ext(config, region, offset, &ci, &y[4],0)?;
            c[x] = ci;
        }

        for x in 0..5 {
            let di = self.rotate_left_cont(config, region, offset, &c[next(x)], 1,BIT_XOR as u64)?;
            let di = self.xor_ext(config, region, offset, &di,&c[prev(x)], BIT_XOR as u64)?;
            self.state[x][0] = self.xor_ext(config, region, offset, &di, &self.state[x][0],0)?;
            for y in 1..5 {
                self.state[x][y] = self.xor(config, region, offset, &self.state[x][y], &di)?;
            }
        }



        /*
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

         */

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
                if rc == 0 {
                    out[x][y] = self.state[x][y].clone(); // save 6 rows per round
                } else {
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
        }



        /*
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

         */
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

        let mut out = self.state.clone();

        // TODO: more elegant
        for y in 0..5 {
            out[0][y] = self.xor_not_and(
                config,
                region,
                offset,
                &self.state[0][y],
                &self.state[next(0usize)][y],
                &self.state[skip(0usize)][y],
            )?;

            out[4][y] = self.xor_not_and_ext(
                config,
                region,
                offset,
                &self.state[4][y],
                &self.state[next(4)][y],
                &self.state[skip(4)][y],
                BIT_NOT_AND as u64,
            )?;

            out[3][y] = self.xor_not_and_ext(
                config,
                region,
                offset,
                &self.state[3][y],
                &self.state[next(3)][y],
                &self.state[skip(3)][y],
                BIT_NOT_AND as u64,
            )?;

            out[2][y] = self.xor_not_and_ext(
                config,
                region,
                offset,
                &self.state[2][y],
                &self.state[next(2)][y],
                &self.state[skip(2)][y],
                BIT_NOT_AND as u64,
            )?;

            out[1][y] = self.xor_not_and_ext(
                config,
                region,
                offset,
                &self.state[1][y],
                &self.state[next(1)][y],
                &self.state[skip(1)][y],
                0,
            )?;
        }
        self.state = out;
        Ok(())



        /*
        let next = |x| (x + 1) % 5;
        let skip = |x| (x + 2) % 5;

        let mut out = self.state.clone();

        for x in 0..5 {
            for y in 0..5 {
                out[x][y] = self.xor_not_and(
                    config,
                    region,
                    offset,
                    &self.state[x][y],
                    &self.state[next(x)][y],
                    &self.state[skip(x)][y],
                )?;
            }
        }
        self.state = out;
        Ok(())
         */


    }

    pub fn iota(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        round: usize,
    ) -> Result<(), Error> {
        let a = self.state[0][0].clone();
        let b = self.rc[round].clone();
        let r = field_to_u64(&a.value) ^ field_to_u64(&b.value);
        let res = Limb::new(None, F::from(r)); // reference
        // self.state[0][0] = self.xor(config, region, offset, &self.state[0][0], &self.rc[round])?;
        config.decompose_bytes(region, offset, &self.state[0][0], 0, BIT_XOR as u64)?;
        config.decompose_bytes(region, offset, &self.rc[round], 0, 0)?;
        let (output, _) = config.decompose_bytes(region, offset, &res, 0, 0)?;

        {
            let a = field_to_u64(&a.value);
            let b = field_to_u64(&b.value);
            let res = a ^ b;
            assert_eq!(F::from(res), output.value);
        }

        self.state[0][0] = output;

        Ok(())
    }

    pub fn iota_cont(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        round: usize,
    ) -> Result<(), Error> {
        let a = self.state[0][0].clone();
        let b = self.rc[round].clone();
        let r = field_to_u64(&a.value) ^ field_to_u64(&b.value);
        let res = Limb::new(None, F::from(r)); // reference
        // self.state[0][0] = self.xor(config, region, offset, &self.state[0][0], &self.rc[round])?;
        config.decompose_bytes(region, offset, &self.state[0][0], 0, BIT_XOR as u64)?;
        config.decompose_bytes(region, offset, &self.rc[round], 0, 0)?;
        let (output, _) = config.decompose_bytes(region, offset, &res, 0, BIT_XOR as u64)?;

        {
            let a = field_to_u64(&a.value);
            let b = field_to_u64(&b.value);
            let res = a ^ b;
            assert_eq!(F::from(res), output.value);
        }

        self.state[0][0] = output;

        Ok(())
    }

    pub fn round(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        round: usize,
    ) -> Result<(), Error> {

        if round == 0 {
            self.theta(config, region, offset)?;
            self.rho(config, region, offset)?;
            self.pi(config, region, offset)?;
            self.xi(config, region, offset)?;
            self.iota_cont(config, region, offset, round)?;
        } else if round == 23 {
            self.iota_theta(config, region, offset)?;
            self.rho(config, region, offset)?;
            self.pi(config, region, offset)?;
            self.xi(config, region, offset)?;
            self.iota(config, region, offset, round)?;
        } else {
            self.iota_theta(config, region, offset)?;
            self.rho(config, region, offset)?;
            self.pi(config, region, offset)?;
            self.xi(config, region, offset)?;
            self.iota_cont(config, region, offset, round)?;
        }



        /*
        self.theta(config, region, offset)?;
        self.rho(config, region, offset)?;
        self.pi(config, region, offset)?;
        self.xi(config, region, offset)?;
        self.iota(config, region, offset, round)?;
        */

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
        //self.debug();
        println!("offset permute {}", offset);
        Ok(())
    }
}
