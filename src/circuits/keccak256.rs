<<<<<<< Updated upstream
use crate::host::keccak256::{ROUND_CONSTANTS, N_R, ROTATION_CONSTANTS, RATE_LANES};
=======
use crate::circuits::bits_arith::BitsArithChip;
use crate::circuits::bits_arith::BitsArithConfig;
use crate::circuits::bits_arith::BIT_NOT_AND;
use crate::circuits::bits_arith::BIT_ROTATE_LEFT;
use crate::circuits::bits_arith::BIT_XOR;
use crate::circuits::{CommonGateConfig, Limb};
use crate::host::keccak256::{N_R, RATE_LANES, ROTATION_CONSTANTS, ROUND_CONSTANTS};

>>>>>>> Stashed changes
use crate::utils::field_to_u64;
use halo2_proofs::arithmetic::FieldExt;

use crate::circuits::{
    CommonGateConfig,
    Limb,
};
use std::marker::PhantomData;
use halo2_proofs::{
    circuit::*,
    plonk::*,
};

#[derive(Debug, Clone)]
pub struct KeccakState<F: FieldExt> {
    state: [[Limb<F>; 5]; 5],
    default: [[Limb<F>; 5]; 5],
}

pub struct KeccakChip<F:FieldExt> {
    pub config: CommonGateConfig,
    keccak_state: KeccakState<F>,
    round: u64,
    _marker: PhantomData<F>
}

impl<F: FieldExt> KeccakChip<F> {
    pub fn construct(config: CommonGateConfig) -> Self {
        let state = [[0u32;5] ;5].map(|x| x.map(|_| Limb::new(None, F::zero())));
        let default = [[0u32;5] ;5].map(|x| x.map(|_| Limb::new(None, F::zero())));
        let state = KeccakState {
            state,
            default,
        };

        KeccakChip {
            round: 0,
            config,
            keccak_state: state, ///mapping rule: S[w(5y+x)+z] = state[x][y][z])]
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

    pub fn configure(cs: &mut ConstraintSystem<F>, shared_advice: &Vec<Column<Advice>>) -> CommonGateConfig {
        CommonGateConfig::configure(cs, &(), shared_advice)
    }

    // assign the r as witness to call the permutation function and constrain the result to be the same as the digest
    pub fn get_permute_result(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
    ) -> Result<Limb<F>, Error> {

        let mut new_state = self.keccak_state.default.clone();
        for (x,(current_state,default)) in (self
            .keccak_state.state
            .iter()
            .zip(self.keccak_state.default.iter())).enumerate()
        {

            for i in 0..5 {
                new_state[x][i] = self.config.select(
                    region,
                    &mut (),
                    offset,
                    &reset,
                    &current_state[i],
                    &default[i],
                    self.round
                )?;
            }
        }

        println!("offset after pick state is {}", offset);

        //absorb
        let chunks_total = values.len() / RATE_LANES;
        for chunk_i in 0..chunks_total {
            let chuck_offset = chunk_i * RATE_LANES;
            let mut x = 0;
            let mut y = 0;

            for i in 0..RATE_LANES {
                new_state[x][y] = self.keccak_state.xor(
                    region,
                    &self.config,
                    offset,
                    &new_state[x][y],
                    &values[i + chuck_offset],
                )?;
                if x < 5 - 1 {
                    x += 1;
                } else {
                    y += 1;
                    x = 0;
                }
            }
        }

        println!("offset after xor state is {}", offset);

        self.keccak_state.state = new_state;

        self.keccak_state.permute(
            &self.config,
            region,
            offset,
        )?;

        let part0 = self.keccak_state.state[0][0].value.clone();
        let part1 = self.keccak_state.state[1][0].value.clone();
        let part2 = self.keccak_state.state[2][0].value.clone();
        let part3 = self.keccak_state.state[3][0].value.clone();

        let part0_limb = Limb::new(None, part0);
        let part1_limb = Limb::new(None, part1);
        let part2_limb = Limb::new(None, part2);
        let part3_limb = Limb::new(None, part3);

        // each part is 64bit and digest is 256bit
        let digest_01 = part0 * F::from_u128(1u128 << 64) + part1;
        let digest_12 = digest_01 * F::from_u128(1u128 << 64) + part2;
        let digest = digest_12 * F::from_u128(1u128 << 64) + part3;

        let digest_limb_01 = self.config.assign_line(
            region,
            &mut (),
            offset,
            [Some(part0_limb), Some(part1_limb), Some(Limb::new(None,digest_01)), None, None, None],
            [Some(F::from_u128(1u128 << 64)), Some(F::one()), Some(-F::one()), None, None, None, None, None, None],
            8,
        )?[2].clone();

        let digest_limb_12 = self.config.assign_line(
            region,
            &mut (),
            offset,
            [Some(digest_limb_01), Some(part2_limb), Some(Limb::new(None,digest_12)), None, None, None],
            [Some(F::from_u128(1u128 << 64)), Some(F::one()), Some(-F::one()), None, None, None, None, None, None],
            8,
        )?[2].clone();

        let digest_limb = self.config.assign_line(
            region,
            &mut (),
            offset,
            [Some(digest_limb_12), Some(part3_limb), Some(Limb::new(None,digest)), None, None, None],
            [Some(F::from_u128(1u128 << 64)), Some(F::one()), Some(-F::one()), None, None, None, None, None, None],
            8,
        )?[2].clone();

        Ok(digest_limb)
    }

    pub(crate) fn assign_permute(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
        result: &Limb<F>,
    ) -> Result<(), Error> {
        println!("offset is {}", offset);
        let r = self.get_permute_result(region, offset, values, reset)?;
        assert_eq!(r.value, result.value);

        region.constrain_equal(
            result.cell.as_ref().unwrap().cell(),
            r.cell.as_ref().unwrap().cell(),
        )?;
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
        let state = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));
        let default = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));
        self.default = default;
        self.state = state;
        Ok(())
    }

    pub fn xor(&self,
        region: &mut Region<F>,
<<<<<<< Updated upstream
=======
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
>>>>>>> Stashed changes
        config: &CommonGateConfig,
        //lookup_assist_chip: &mut LC,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
) -> Result<Limb<F>, Error> {

<<<<<<< Updated upstream
        let res = Limb::new(None, F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)));

        let mut bit_limb_lhs = vec![];
        let mut bit_limb_rhs = vec![];
        let mut bit_limb_res = vec![];

        config.decompose_limb(region,&mut(), offset, &lhs, &mut bit_limb_lhs, 64)?;
        config.decompose_limb(region,&mut(), offset, &rhs, &mut bit_limb_rhs, 64)?;
        config.decompose_limb(region,&mut(), offset, &res, &mut bit_limb_res, 64)?;
        
        let mut bit_array_limb_lhs = Vec::with_capacity(64);
        let mut bit_array_limb_rhs = Vec::with_capacity(64);
        let mut bit_array_limb_res = Vec::with_capacity(64);

        for x in 0..64 {
            bit_array_limb_lhs.push(field_to_u64(&bit_limb_lhs[x].value));
            bit_array_limb_rhs.push(field_to_u64(&bit_limb_rhs[x].value));
            bit_array_limb_res.push(field_to_u64(&bit_limb_res[x].value));
        }

        let mut res_limb = Limb::new(None,F::zero());
        let mut lhs_limb = Limb::new(None,F::zero());
        let mut rhs_limb = Limb::new(None,F::zero());

        for (i, &bit) in bit_array_limb_res.iter().rev().enumerate() {
            res_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }
        for (i, &bit) in bit_array_limb_lhs.iter().rev().enumerate() {
            lhs_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }
        for (i, &bit) in bit_array_limb_rhs.iter().rev().enumerate() {
            rhs_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }

        let encode_limb = Limb::new(None, lhs_limb.value * F::from_u128(1 << 16) + rhs_limb.value * F::from_u128(1 << 8) + res_limb.value);

        let res_vec = config.assign_line(region, &mut (), offset,
                                         [Some(lhs_limb), Some(rhs_limb), Some(res_limb), Some(encode_limb), None, None],
                                         [Some(F::from_u128(1u128 << 16)), Some(F::from_u128(1u128 << 8)), Some(F::one()), Some(-F::one()),None, None, None, None, None], 8)?;
        Ok(res_vec[2].clone())
    }
    
=======
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

>>>>>>> Stashed changes
    pub fn rotate_left(
        &self,
        region: &mut Region<F>,
        config: &CommonGateConfig,
        offset: &mut usize,
        input: &Limb<F>,
        n: usize,
    ) -> Result<Limb<F>, Error> {
        
        let mut bit_limb = vec![];
        config.decompose_limb(region,&mut(), offset, &input, &mut bit_limb, 64)?;
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
        
        let mut res_limb1 = Limb::new(None,F::zero());
        let mut res_limb2 = Limb::new(None,F::zero());
        
        for (i, bit) in bit_limb1.iter().rev().enumerate() { // little endian
            res_limb1.value += bit.value * F::from_u128(1 << i);
        }

        for (i, bit) in bit_limb2.iter().rev().enumerate() {
            res_limb2.value += bit.value * F::from_u128(1 << i);
        }

        // res_limb1.value + res_limb2.value * F::from_u128(1 << n) - rotate_res_limb.value = 0;
        let res = config.assign_line(region, &mut (), offset, 
        [Some(res_limb1), Some(res_limb2), None, None, Some(rotate_res_limb), None], 
        [Some(F::one()), Some(F::from_u128(1 << n)), None, None, Some(-F::one()), None, None, None, None], 0)?;
        
        Ok(res[2].clone())

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
<<<<<<< Updated upstream
=======

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
>>>>>>> Stashed changes

        let mut c = self.default[0].clone();
        //let mut d = [[0u32;5];5].map(|x| x.map(|_|zero.clone()) );
        let mut d = self.default.clone();

        for x in 0..5 {
            let state_u64 = field_to_u64(&self.state[x][0].value) ^ field_to_u64(&self.state[x][1].value) ^ field_to_u64(&self.state[x][2].value) ^ field_to_u64(&self.state[x][3].value) ^ field_to_u64(&self.state[x][4].value);
            c[x] = Limb::new(None,F::from(state_u64));
        }
        for x in 0..5 {
            for y in 0..5 {
                let rotate_limb = self.rotate_left(region, config, offset, &c[(x+1)%5], 1)?;
                d[x][y] = Limb::new(None,F::from(field_to_u64(&c[(x+4)%5].value) ^ field_to_u64(&rotate_limb.value)));
            }
        }

        for x in 0..5 {
            for y in 0..5 {
                self.state[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ field_to_u64(&d[x][y].value)));
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
<<<<<<< Updated upstream
                let rotate_limb = self.rotate_left(region, config, offset, &self.state[x][y], rc.try_into().unwrap())?;
=======
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
>>>>>>> Stashed changes
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

    // maybe use lookup table to optimize? limb, not limb and encode limb
    pub fn xi(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
<<<<<<< Updated upstream
=======

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

>>>>>>> Stashed changes
        let mut out = self.state.clone();

        for x in 0..5 {
            for y in 0..5 {
                //not operation
                let target_limb = self.state[(x + 1) % 5][y].clone();
                let mut bit_array_limb = Vec::new();
                let mut bit_state = vec![]; // in big endian
                config.decompose_limb(region,&mut(), offset, &target_limb, &mut bit_state, 64)?;

                for x in 0..64 {
                    bit_array_limb.push(field_to_u64(&bit_state[x].value));
                }

                let mut not_limb = Limb::new(None,F::zero());
                for i in 0..bit_array_limb.len() {
                    bit_array_limb[i] = 1 - bit_array_limb[i];
                }
                //add constraint
                for (i, &bit) in bit_array_limb.iter().rev().enumerate() {
                    not_limb.value += F::from_u128( bit as u128) * F::from_u128(1 << i);
                }

                let res_limb = Limb::new(None,F::from(field_to_u64(&target_limb.value) ^ field_to_u64(&not_limb.value)));
                let encode_limb = Limb::new(None, *&self.state[(x + 1) % 5][y].value * F::from_u128(1 << 16) + not_limb.value * F::from_u128(1 << 8) + res_limb.value);

                let res_vec = config.assign_line(region, &mut (), offset,
                                                 [Some(target_limb), Some(not_limb), Some(res_limb), Some(encode_limb), None, None],
                                                 [Some(F::from_u128(1u128 << 16)), Some(F::from_u128(1u128 << 8)), Some(F::one()), Some(-F::one()), None, None, None, None, None], 8)?;

                out[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ (field_to_u64(&res_vec[1].value.clone()) & field_to_u64(&self.state[(x + 2) % 5][y].value))));
                //out[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ !field_to_u64(&self.state[(x + 1) % 5][y].value) & field_to_u64(&self.state[(x + 2) % 5][y].value)));
            }
        }
        self.state = out;
        Ok(())
         */


    }

    pub fn iota(
        &mut self,
        _config: &CommonGateConfig,
        _region: &mut Region<F>,
        _offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {
<<<<<<< Updated upstream
        let mut out = self.state.clone();
        out[0][0] = Limb::new(None,F::from(field_to_u64(&out[0][0].value) ^ rc));

        self.state = out;
=======
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

>>>>>>> Stashed changes
        Ok(())
    }

    pub fn round(&mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {

<<<<<<< Updated upstream
=======
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
>>>>>>> Stashed changes
        self.theta(config, region, offset)?;
        self.rho(config, region, offset)?;
        self.pi(config, region, offset)?;
        self.xi(config, region, offset)?;
<<<<<<< Updated upstream
        self.iota(config, region, offset, rc)?;
=======
        self.iota(config, region, offset, round)?;
        */
>>>>>>> Stashed changes

        Ok(())


    }

    pub fn permute(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
<<<<<<< Updated upstream
       
        for rc in ROUND_CONSTANTS.iter().take(N_R) {
            Self::round(self, config, region, offset, *rc)?;
=======
        for round in 0..N_R {
           Self::round(self, config, region, offset, round)?;
>>>>>>> Stashed changes
        }
        //self.debug();
        println!("offset permute {}", offset);
        Ok(())
    }
}
