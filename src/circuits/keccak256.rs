use crate::host::keccak256::*;
use crate::utils::*;

use halo2_proofs::arithmetic::FieldExt;
use ripemd::digest::typenum::bit;

use crate::circuits::{
    CommonGateConfig,
    Limb,
};

use std::{marker::PhantomData};

use halo2_proofs::{
    circuit::{Region, AssignedCell, Layouter},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
};

pub struct KeccakState<F: FieldExt> {
    state: [[Limb<F>; 5]; 5],
}

pub struct KeccakChip<F:FieldExt> {
    pub config: CommonGateConfig,
    keccak_state: KeccakState<F>,
    round: u64,
    _marker: PhantomData<F>
}

pub struct Spec {
    rate: usize,
    capacity: usize,
}

impl<F: FieldExt> KeccakChip<F> {
    pub fn construct(config: CommonGateConfig) -> Self {
        let state = [[0u32;5] ;5].map(|x| x.map(|_| Limb::new(None, F::zero())));
        let state = KeccakState {
            state,
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


    pub fn assign_permute( // assign the r as witness to the circuit and call the permutation function
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE],
        result: &Limb<F>,
    ) -> Result<(), Error> {
        println!("offset is: {:?}", offset);
        println!("input values: {:?}", values.iter().map(|x| x.value).collect::<Vec<_>>());
        let zero = self.config.assign_constant(region, &mut (), offset, &F::zero())?;
        let mut inputs = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));

        for (x,y) in self.keccak_state.state.iter().enumerate() {
            let state_row = y.clone().map(|y| {Some(y)}).to_vec();
            print!("state_col: {:?} ",state_row);
          
            let mut input = self.config.assign_witness(
                region,
                &mut (),
                offset,
                state_row.try_into().unwrap(),
                0,
            )?;

            inputs[x] = input.try_into().unwrap();
        }

        self.keccak_state.permute(
            &self.config,
            region,
            offset,
            &inputs,
        )?;

        //println!("expect {:?}, get {:?}", result.value, self.keccak_state.state[1].value);
        //assert!(self.keccak_state.state[1].value == result.value);
    
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
        let mut state = [[0u32;5];5].map(|x| x.map(|_|zero.clone()));
        self.state = state;
        Ok(())
    }

    
    pub fn xor(&self,
        region: &mut Region<F>,
        config: &CommonGateConfig,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Limb<F>,
) -> Result<Limb<F>, Error> {
        let res = Limb::new(None, F::from(field_to_u64(&lhs.value) ^ field_to_u64(&rhs.value)));
        // a + b - 2 * a * b - c = 0

        let xor_vec = config.assign_line(
            region,
            &mut (),
            offset, [Some(lhs.clone()), Some(res.clone()), None, Some(rhs.clone()), None, None],
            [Some(F::one()), Some(-F::one()), None, Some(F::one()), None, None, Some(F::from_u128(2)), None, None],
            0,
        )?;

        Ok(xor_vec[1].clone()) // c
    }
    
    pub fn rotate_left(
        &self,
        region: &mut Region<F>,
        config: &CommonGateConfig,
        offset: &mut usize,
        input: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        
        let mut bit_limb = vec![];
        config.decompose_limb(region,&mut(), offset, &input, &mut bit_limb, 64);
        
        let temp = bit_limb.pop().unwrap();
        bit_limb.insert(0, temp);
        let mut acc = Limb::new(None, F::zero());
        //construct the limb from the bits
        for (i, bit) in bit_limb.iter().enumerate() {
            
            acc.value += bit.value * F::from_u128(1 << i);
            //Add the constraints b_out[0] = b_in[(0+1) mod 64] = b_in[1]
        }
        Ok(acc)
        }


    pub fn theta(
        &mut self,
        config: &CommonGateConfig,
        //bit_state: &mut Vec<Limb<F>>,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero= config.assign_constant(region, &mut (), offset, &F::zero())?;
  
        let mut C = [0u32;5].map(|_| zero.clone());
        let mut D = [0u32;5].map(|_| zero.clone());
        let mut out = [[0u32; 5]; 5].map(|f| f.map(|_| zero.clone()));
        
        for x in 0..5 {
            let state_u64 = field_to_u64(&self.state[x][0].value) ^ field_to_u64(&self.state[x][1].value) ^ field_to_u64(&self.state[x][2].value) ^ field_to_u64(&self.state[x][3].value) ^ field_to_u64(&self.state[x][4].value);
            // do we need to add the constraints here?
            C[x] = Limb::new(None,F::from(state_u64));
        }   

        //TODO: constraint C
        for x in 0..5 {
            let mut bit_array_limb = Vec::with_capacity(64);
            let mut bit_state = vec![];
            config.decompose_limb(region,&mut(), offset, &C[(x+4)%5], &mut bit_state, 64);
            
            for x in 0..64 {
                bit_array_limb.push(field_to_u64(&bit_state[x].value));
            }

            bit_array_limb.rotate_left(1);

            let mut rotate_limb = Limb::new(None,F::zero());
            for x in bit_array_limb.iter() {
                rotate_limb.value += F::from_u128(1 << x);
            }
            D[x] = Limb::new(None,F::from(field_to_u64(&C[(x+4)%5].value) ^ field_to_u64(&rotate_limb.value)));
        }
        
        for x in 0..5 {
            for y in 0..5 {
                self.state[x][y] = Limb::new(None,F::from(field_to_u64(&self.state[x][y].value) ^ field_to_u64(&D[x].value)));
            }
        }
        // Constraint the XOR operation by check each element of lhs and rhs after XOR to be the same as the result

        Ok(())
    }


    pub fn rho(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let mut out = self.state.clone();

        for x in 0..5 {
            for y in 0..5 {
                let rc = ROTATION_CONSTANTS[x][y];
                let mut bit_array_limb = Vec::with_capacity(64);
                let mut bit_state = vec![];
                config.decompose_limb(region,&mut(), offset, &out[x][y], &mut bit_state, 64);
                
                for x in 0..64 {
                    bit_array_limb.push(field_to_u64(&bit_state[x].value));
                }

                bit_array_limb.rotate_left(rc.try_into().unwrap());

                /// Constraint the rotate left by check if the first bit of the limb is the last bit of the rotate_limb

                let mut rotate_limb = Limb::new(None,F::zero());
                for x in bit_array_limb.iter() {
                    rotate_limb.value += F::from_u128(1 << x);
                }

                // Constraint the process of constructing the limb from the bits
                
                self.state[x][y] = rotate_limb;
            }
        }

        Ok(())

    }


    pub fn pi(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let mut out = self.state.clone();

        for x in 0..5 {
            for y in 0..5 {
                self.state[y][(2 * x + 3 * y) % 5] = out[x][y];
            }
        }
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
                let mut bit_state = vec![];
                config.decompose_limb(region,&mut(), offset, &out[(x + 1) % 5][y], &mut bit_state, 64);

                for x in 0..64 {
                    bit_array_limb.push(field_to_u64(&bit_state[x].value));
                }

                let mut not_limb = Limb::new(None,F::zero());
                for x in 0..bit_array_limb.len() {
                    bit_array_limb[x] = !bit_array_limb[x];
                    not_limb.value += F::from_u128(1 << bit_array_limb[x]); 
                }
               
                self.state[x][y] = Limb::new(None,F::from(field_to_u64(&out[x][y].value) ^ (field_to_u64(&not_limb.value) & field_to_u64(&out[(x + 2) % 5][y].value))));
            }
        }
        Ok(())
    }

    pub fn iota(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {
        let mut out = self.state.clone();
        self.state[0][0] = Limb::new(None,F::from(field_to_u64(&out[0][0].value) ^ rc));
        
        Ok(())
    }
    
    pub fn round(&mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        rc: u64,
    ) -> Result<(), Error> {

        let mut out = self.state.clone();
        let mut bit_state = vec![];
        out.map(|f| f.map(|x| config.decompose_limb(region,&mut(), offset, &x, &mut bit_state, 64)));
        
        self.theta(config, region, offset);
        self.rho(config, region, offset);
        self.pi(config, region, offset);
        self.xi(config, region, offset);
        self.iota(config, region, offset,rc);

        Ok(())
    }

    pub fn permute(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        inputs: &[[Limb<F>; 5];5],
    ) -> Result<(), Error> {
       
        for rc in ROUND_CONSTANTS.iter().take(N_R) {
            Self::round(self, config, region, offset, *rc);
        }

        Ok(())
    }

    // TODO: implement padding
    // TODO: XOR
    fn u8_to_bits(num: u8) -> Vec<bool> {
        let mut result = Vec::with_capacity(8);
        let mut n = num;
        for _ in 0..8 {
            result.push(n & 1 == 1);
            n >>= 1;
        }
        result
    }

    fn bits_to_limbs(message: &Vec<bool>) -> Vec<Limb<F>> {
        let limb_total = message.len() / 64;
        let mut limbs:Vec<Limb<F>> = vec![0; limb_total].iter().map(|x| Limb::new(None, F::zero())).collect();

        for i in 0..limb_total {
            for j in 0..64 {
                //TODO: convert bool to F
                if message[i * 64 + j] {
                    limbs[i].value += F::from_u128(1 << j);
                }
            }
        }
        limbs
    }

    fn padding(input: &[u8]) -> Vec<Limb<F>> {

        let chunk_size_in_bytes = 136; // in bytes
        let num_chunks = input.len() / chunk_size_in_bytes + 1;
        let len_to_pad = chunk_size_in_bytes - input.len() % chunk_size_in_bytes;
        dbg!(num_chunks);

        let mut padded = vec![];
        for i in 0..input.len() * 8 {
            let bit: Vec<bool> = Self::u8_to_bits(input[i]).try_into().unwrap();
            for x in 0..bit.len() {
                padded.push(bit[x]);
            }
        }

        padded.push(true);

        for i in 0..len_to_pad * 8 - 2 {
            padded.push(false);
        }

        padded.push(true);

        let result = Self::bits_to_limbs(&padded);
        assert!(num_chunks == result.len());
        result
    }

    

    pub fn absorb(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE], //after padding
        pre_constants: &[F; T],
    ) -> Result <(), Error> {
        debug_assert!(
            inputs.len() % RATE == 0,
            "Message is not divisible entirely by RATE"
        );

        let total_chunks = inputs.len() / RATE;
        let out = self.state.clone();
        
        for chunk_i in 0..total_chunks {
            let chunk_offset: usize = chunk_i * (RATE / 8);
            let mut x = 0;
            let mut y = 0;
            for i in 0..(RATE / 8) {
                let input = inputs[chunk_offset + i];
                self.state[x][y] = Limb::new(None, F::from(field_to_u64(&out[x][y].value) ^ field_to_u64(&input.value)));
                if x < 5 - 1 {
                    x += 1;
                } else {
                    y += 1;
                    x = 0;
                }
            }
            self.permute(
                config,
                region,
                offset,
                &self.state,
                );
        }
        Ok(())
    }

}

mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;
    use crate::host::keccak256::RATE;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

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
            let v = if reset {Fr::one()} else {Fr::zero()};
            let c = region.assign_advice(
                || format!("assign input"),
                self.config.limb,
                *offset,
                || value_for_assign!(v)
            )?;
            *offset += 1;
            Ok(Limb::new(Some(c), v))
        }


        fn assign_inputs(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            inputs: &[Fr; RATE],
        ) -> Result<[Limb<Fr>; RATE], Error> {
            let r = inputs.map(|x| {
                let c = region.assign_advice(
                    || format!("assign input"),
                    self.config.limb,
                    *offset,
                    || value_for_assign!(x.clone())
                ).unwrap();
                *offset += 1;
                Limb::new(Some(c), x.clone())
            });
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
                || "assign poseidon test",
                |mut region| {
                    let mut offset = 0;
                    let result = helperchip.assign_result(&mut region, &mut offset, &self.result)?;
                    let inputs = helperchip.assign_inputs(&mut region, &mut offset, &self.inputs.clone().try_into().unwrap())?;
                    let reset = helperchip.assign_reset(&mut region, &mut offset, true)?;
                    offset = 0;
                    keccakchip.keccak_state.initialize(&config.keccakconfig, &mut region, &mut offset)?;
                    keccakchip.assign_permute(
                        &mut region,
                        &mut offset,
                        &inputs,
                        &result
                    )?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

}