use crate::host::keccak256::{ROUND_CONSTANTS, N_R, ROTATION_CONSTANTS, RATE_LANES};
use crate::utils::*;

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

    pub fn configure(cs: &mut ConstraintSystem<F>) -> CommonGateConfig {
        CommonGateConfig::configure(cs, &())
    }

    // assign the r as witness to call the permutation function and constrain the result to be the same as the digest
    pub fn get_permute_result(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE_LANES],
        reset: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        let zero = self.config.assign_constant(region, &mut (), offset, &F::zero())?;
        let mut new_state = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));


        for (x,(y,default)) in (self
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
                    &y[i],
                    &default[i],
                    self.round
                )?;
            }
        }

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
                    &self.keccak_state.state[x][y],
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

        self.keccak_state.state = new_state;

        for y in  self.keccak_state.state.iter() {
            dbg!(&y);
        }
        //self.keccak_state.state[0][0].value = F::one();
        self.keccak_state.permute(
            &self.config,
            region,
            offset,
        )?;

        let part0 = self.keccak_state.state[0][0].value.clone();
        let part1 = self.keccak_state.state[1][0].value.clone();
        let part2 = self.keccak_state.state[2][0].value.clone();
        let part3 = self.keccak_state.state[3][0].value.clone();

        // each part is 64bit and digest is 256bit
        let digest = ((part0 * F::from_u128(1u128 << 64) + part1)
            * F::from_u128(1u128 << 64) + part2)
            * F::from_u128(1u128 << 64) + part3;

        let digest_limb = self.config.assign_constant(
            region,
            &mut (),
            offset,
            &digest,
        )?;

        //region.constrain_equal(result.cell.as_ref().unwrap().cell(), digest_limb.cell.as_ref().unwrap().cell())?;
        dbg!(digest);
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
        let r = self.get_permute_result(region, offset, values, reset)?;
        println!("expect {:?}, get {:?}", &result.value, &r.value);
        assert_eq!(r.value, result.value);

        region.constrain_equal(
            result.cell.as_ref().unwrap().cell(),
            r.cell.as_ref().unwrap().cell(),
        )?;
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
        *offset = 0;
        let zero = config.assign_constant(region, &mut (), offset, &F::zero())?;
        let state = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));
        let default = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));
        self.default = default;
        self.state = state;
        Ok(())
    }

    pub fn xor(&self,
        region: &mut Region<F>,
        config: &CommonGateConfig,
        //lookup_assist_chip: &mut LC,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
) -> Result<Limb<F>, Error> {

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
            bit_array_limb_lhs.push(field_to_u64(&bit_limb_lhs[63-x].value));
            bit_array_limb_rhs.push(field_to_u64(&bit_limb_rhs[63-x].value));
            bit_array_limb_res.push(field_to_u64(&bit_limb_res[63-x].value));
        }

        let mut res_limb = Limb::new(None,F::zero());
        let mut lhs_limb = Limb::new(None,F::zero());
        let mut rhs_limb = Limb::new(None,F::zero());

        /*
        for x in 0..8 {
            for y in 0..8 {
                res_limb.value += F::from_u128(1 << bit_array_limb_res[x * 8 + y]);
                lhs_limb.value += F::from_u128(1 << bit_array_limb_lhs[x * 8 + y]);
                rhs_limb.value += F::from_u128(1 << bit_array_limb_rhs[x * 8 + y]);
            }
        }
        */

        for (i, &bit) in bit_array_limb_res.iter().rev().enumerate() {
            res_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }
        for (i, &bit) in bit_array_limb_lhs.iter().rev().enumerate() {
            lhs_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }
        for (i, &bit) in bit_array_limb_rhs.iter().rev().enumerate() {
            rhs_limb.value += F::from_u128(bit as u128) * F::from_u128(1 << i);
        }

        let encode_limb = Limb::new(None,lhs_limb.value * F::from_u128(1 << 16) + rhs_limb.value * F::from_u128(1 << 8) + res_limb.value);

        let res_vec = config.assign_line(region, &mut (), offset,
                                         [Some(encode_limb),Some(lhs_limb), Some(rhs_limb), Some(res_limb), None, None],
                                         [Some(-F::one()), Some(F::from_u128(1u128 << 16)), Some(F::from_u128(1u128 << 8)), Some(F::one()), None, None, None, None, None], 8)?;
        Ok(res_vec[3].clone())
    }
    
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

        //dbg!(bit_array_limb.clone());

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

        //dbg!(res_limb1.value);
        //dbg!(res_limb2.value);
        //dbg!(rotate_res_limb.value);

        // res_limb1.value + res_limb2.value * F::from_u128(1 << n) - rotate_res_limb.value = 0;
        let res = config.assign_line(region, &mut (), offset, 
        [Some(res_limb1), Some(res_limb2), None, None, Some(rotate_res_limb), None], 
        [Some(F::one()), Some(F::from_u128(1 << n)), None, None, Some(-F::one()), None, None, None, None], 0)?;
        
        Ok(res[2].clone())

        }


    pub fn theta(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero= config.assign_constant(region, &mut (), offset, &F::zero())?;
  
        let mut C = [0u32;5].map(|_| zero.clone());
        let mut D = [[0u32;5];5].map(|x| x.map(|_|zero.clone()) );
        //let mut out = [[0u32;5];5].map(|x| x.map(|_|zero.clone()) );
        
        for x in 0..5 {
            let state_u64 = field_to_u64(&self.state[x][0].value) ^ field_to_u64(&self.state[x][1].value) ^ field_to_u64(&self.state[x][2].value) ^ field_to_u64(&self.state[x][3].value) ^ field_to_u64(&self.state[x][4].value);
            // do we need to add the constraints here?
            C[x] = Limb::new(None,F::from(state_u64));
        }
        dbg!(&C);
        for x in 0..5 {
            for y in 0..5 {
                let rotate_limb = self.rotate_left(region, config, offset, &C[(x+1)%5], 1)?;
                D[x][y] = Limb::new(None,F::from(field_to_u64(&C[(x+4)%5].value) ^ field_to_u64(&rotate_limb.value)));
            }
        }

        for x in 0..5 {
            for y in 0..5 {
                self.state[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ field_to_u64(&D[x][y].value)));
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
        let zero= config.assign_constant(region, &mut (), offset, &F::zero())?;
        let mut out = [[0u32;5];5].map(|x| x.map(|_|zero.clone()) );

        for x in 0..5 {
            for y in 0..5 {
                let rc = ROTATION_CONSTANTS[x][y];
                let rotate_limb = self.rotate_left(region, config, offset, &self.state[x][y], rc.try_into().unwrap())?;
                out[x][y] = rotate_limb;
            }
        }

        self.state = out;

        Ok(())
    }


    pub fn pi(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero= config.assign_constant(region, &mut (), offset, &F::zero())?;
        let mut out = [[0u32;5];5].map(|x| x.map(|_|zero.clone()) );

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
        let mut out = self.state.clone();

        for x in 0..5 {
            for y in 0..5 {
                //not operation
                let mut bit_array_limb = Vec::with_capacity(64);
                let mut bit_state = vec![]; // in big endian
                config.decompose_limb(region,&mut(), offset, &self.state[(x + 1) % 5][y], &mut bit_state, 64)?;

                for x in 0..64 {
                    bit_array_limb.push(field_to_u64(&bit_state[x].value));
                }

                let mut not_limb = Limb::new(None,F::zero());
                for i in 0..bit_array_limb.len() {
                    bit_array_limb[i] = !bit_array_limb[i];
                }

                for (i, &bit) in bit_array_limb.iter().rev().enumerate() {
                    not_limb.value += F::from_u128( bit as u128) * F::from_u128(1 << i);
                }

                out[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ (field_to_u64(&not_limb.value) & field_to_u64(&self.state[(x + 2) % 5][y].value))));
            }
        }

        self.state = out;
        Ok(())
    }

    pub fn iota(
        &mut self,
        _config: &CommonGateConfig,
        _region: &mut Region<F>,
        _offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {
        let mut out = self.state.clone();
        out[0][0] = Limb::new(None,F::from(field_to_u64(&out[0][0].value) ^ rc));

        self.state = out;
        Ok(())
    }
    
    pub fn round(&mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {
        for state_before_round in self.state.iter() {
            dbg!(&state_before_round);
        }

        self.theta(config, region, offset)?;
        self.rho(config, region, offset)?;
        self.pi(config, region, offset)?;
        self.xi(config, region, offset)?;
        self.iota(config, region, offset,rc)?;

        Ok(())
    }

    pub fn permute(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
       
        for rc in ROUND_CONSTANTS.iter().take(N_R) {
            Self::round(self, config, region, offset, *rc)?;
        }

        Ok(())
    }
}

mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use crate::{host, value_for_assign};
    use crate::circuits::CommonGateConfig;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };
    use halo2_proofs::arithmetic::FieldExt;

    use super::{
        KeccakChip,
        Limb,
    };

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig
    }

    impl Chip<Fr> for HelperChip {
        type Config = HelperChipConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }

    impl HelperChip {
        fn new(config: HelperChipConfig) -> Self {
            HelperChip{
                config,
            }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let limb= cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_reset(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            reset: bool,
        ) -> Result<Limb<Fr>, Error> {
            let v = if reset { Fr::one() } else { Fr::zero() };
            let c = region.assign_advice(
                || format!("assign reset"),
                self.config.limb,
                *offset,
                || value_for_assign!(v),
            )?;
            *offset += 1;
            Ok(Limb::new(Some(c), v))
        }

        fn assign_inputs(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            inputs: &Vec<Fr>
        ) -> Result<Vec<Limb<Fr>>, Error> {
            let r: Vec<Limb<Fr>> = inputs.
                iter()
                .map(|x| {
                    let c = region.assign_advice(
                        || format!("assign input"),
                        self.config.limb,
                        *offset,
                        || value_for_assign!(x.clone())
                    ).unwrap();
                    *offset += 1;
                    Limb::new(Some(c), x.clone())
                }).collect();
                
            Ok(r)
        }


        fn assign_result(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            result: &Fr,
        ) -> Result<Limb<Fr>, Error> {
            
            let c = region.assign_advice(
                || format!("assign input"),
                self.config.limb,
                *offset,
                || value_for_assign!(result.clone())
            )?;
            *offset += 1;
            Ok(Limb::new(Some(c), result.clone()))
        }

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        inputs: Vec<Fr>,
        result: Fr,
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        keccakconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            Self::Config {
               keccakconfig: KeccakChip::<Fr>::configure(meta),
               helperconfig: HelperChip::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let mut keccakchip = KeccakChip::<Fr>::construct(config.clone().keccakconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "assign keccak test",
                |mut region| {
                    let mut offset = 0;
                    let result = helperchip.assign_result(&mut region, &mut offset, &self.result)?;
                    let reset = helperchip.assign_reset(&mut region, &mut offset, true)?;
                    let inputs = helperchip.assign_inputs(&mut region, &mut offset, &self.inputs.clone())?;
                    offset = 0;

                    keccakchip.keccak_state.initialize(&config.keccakconfig, &mut region, &mut offset)?;

                    keccakchip.assign_permute(
                        &mut region,
                        &mut offset,
                        &inputs.try_into().unwrap(),
                        &reset,
                        &result
                    )?;
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_keccak_circuit_00() {
        let mut hasher = host::keccak256::KECCAK_HASHER.clone();
        let result = hasher.squeeze();
        let mut inputs = [0u32;17].map(|_| Fr::zero()).to_vec();
        inputs[16] = Fr::from_u128(1u128 << 63);
        inputs[0] = Fr::one();
        let test_circuit = TestCircuit { inputs, result };
        println!("result is {:?}", result);
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}