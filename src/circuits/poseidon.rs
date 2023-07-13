use crate::host::poseidon::PREFIX_CHALLENGE;
use crate::host::poseidon::PREFIX_POINT;
use crate::host::poseidon::PREFIX_SCALAR;
use crate::host::poseidon::RATE;
use crate::host::poseidon::R_F;
use crate::host::poseidon::R_P;
use crate::host::poseidon::T;
use halo2_proofs::arithmetic::FieldExt;
use poseidon::SparseMDSMatrix;
use poseidon::Spec;

use crate::circuits::{
    CommonGateConfig,
    Limb,
};

use std::marker::PhantomData;

use halo2_proofs::{
    circuit::Region,
    plonk::{
        ConstraintSystem,
        Error
    },
};

pub struct PoseidonState<F: FieldExt> {
    state: [Limb<F>; T],
    default: [Limb<F>; T],
    prefix: Vec<Limb<F>>,
}

pub struct PoseidonChip<F:FieldExt> {
    pub config: CommonGateConfig,
    pub spec: Spec<F, T, RATE>,
    poseidon_state: PoseidonState<F>,
    round: u64,
    _marker: PhantomData<F>
}

impl<F: FieldExt> PoseidonChip<F> {
    pub fn construct(config: CommonGateConfig) -> Self {
        let state = [0u32;T].map(|_| Limb::new(None, F::zero()));
        let state = PoseidonState {
            default: state.clone(),
            state,
            prefix: vec![],
        };

        PoseidonChip {
            round: 0,
            config,
            spec: Spec::new(R_F, R_P),
            poseidon_state: state,
            _marker: PhantomData,
        }
    }

    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.poseidon_state.initialize(config, region, offset)
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> CommonGateConfig {
        CommonGateConfig::configure(cs, &())
    }

    pub (crate) fn get_permute_result(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE],
        reset: &Limb<F>,
    ) -> Result<Limb<F>, Error> {
        let mut new_state = vec![];
        for (value, default) in self.poseidon_state.state.iter().zip(self.poseidon_state.default.iter()) {
            new_state.push(self.config.select(region, &mut (), offset, &reset, value, default, self.round)?);
        }
        self.poseidon_state.state = new_state.try_into().unwrap();
        let parts = values.clone().map(|x| {Some(x)});
        let parts = parts.chunks(4).collect::<Vec<_>>();
        let mut part0 = parts[0].to_vec();
        let mut part1 = parts[1].to_vec();
        part0.push(None);
        part1.push(None);
        let mut inputs = self.config.assign_witness(
            region,
            &mut (),
            offset,
            part0.try_into().unwrap(),
            0,
        )?;
        inputs.append(&mut self.config.assign_witness(
            region,
            &mut (),
            offset,
            part1.try_into().unwrap(),
            0,
        )?);
        self.poseidon_state.permute(
            &self.config,
            &self.spec,
            region,
            offset,
            &inputs.try_into().unwrap(),
        )?;
        Ok(self.poseidon_state.state[1].clone())
    }


    pub fn assign_permute(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        values: &[Limb<F>; RATE],
        reset: &Limb<F>,
        result: &Limb<F>,
    ) -> Result<(), Error> {
        let r = self.get_permute_result(region, offset, values, reset)?;
        assert!(r.value == result.value);
        region.constrain_equal(
            result.cell.as_ref().unwrap().cell(),
            r.cell.as_ref().unwrap().cell()
        )?;
        Ok(())
    }
}

impl<F: FieldExt> PoseidonState<F> {
    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        *offset = 0;
        let zero = config.assign_constant(region, &mut (), offset, &F::zero())?;
        let mut state = [0u32;T].map(|_| zero.clone());
        state[0] = config.assign_constant(region, &mut (), offset, &F::from_u128(1u128<<64))?;
        self.default = state.clone();
        self.state = state;
        self.prefix = vec![
                config.assign_constant(region, &mut (), offset, &F::from(PREFIX_CHALLENGE))?,
                config.assign_constant(region, &mut (), offset, &F::from(PREFIX_POINT))?,
                config.assign_constant(region, &mut (), offset, &F::from(PREFIX_SCALAR))?,
            ];
        Ok(())
    }

    fn x_power5_with_constant(
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        x: &Limb<F>,
        constant: F,
    ) -> Result<Limb<F>, Error> {
        let xx = config.assign_line(region, &mut (), offset,
            [
                Some(x.clone()),
                None,
                None,
                Some(x.clone()),
                Some(Limb::new(None, x.value * x.value)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0,
        )?[2].clone();
        let x4 = config.assign_line(region, &mut (), offset,
            [
                Some(xx.clone()),
                None,
                None,
                Some(xx.clone()),
                Some(Limb::new(None, xx.value * xx.value)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0,
        )?[2].clone();
        let x5 = config.assign_line(region, &mut (), offset,
            [
                Some(x.clone()),
                None,
                None,
                Some(x4.clone()),
                Some(Limb::new(None, x4.value * x.value + constant)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, Some(constant)],
            0,
        )?[2].clone();
        Ok(x5)
    }

    fn sbox_full(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        constants: &[F; T]
    ) -> Result<(), Error> {
        for (x, constant) in self.state.iter_mut().zip(constants.iter()) {
            *x = Self::x_power5_with_constant(config, region, offset, x, *constant)?;
        }
        Ok(())
    }

    fn sbox_part(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        constant: &F
    ) -> Result<(), Error> {
        self.state[0] = Self::x_power5_with_constant(
            config,
            region,
            offset,
            &self.state[0],
            constant.clone()
        )?;
        Ok(())
    }

    pub fn permute(
        &mut self,
        config: &CommonGateConfig,
        spec: &Spec<F, T, RATE>,
        region: &mut Region<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE],
    ) -> Result<(), Error> {
        let r_f = R_F / 2;
        let mds = &spec.mds_matrices().mds().rows();

        let constants = &spec.constants().start();
        self.absorb_with_pre_constants(config, region, offset, inputs, &constants[0])?;

        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.sbox_full(config, region, offset, constants)?;
            self.apply_mds(config, region, offset, mds)?;
        }

        let pre_sparse_mds = &spec.mds_matrices().pre_sparse_mds().rows();
        self.sbox_full(config, region, offset,constants.last().unwrap())?;
        self.apply_mds(config, region, offset, &pre_sparse_mds)?;

        let sparse_matrices = &spec.mds_matrices().sparse_matrices();
        let constants = &spec.constants().partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.sbox_part(config, region, offset, constant)?;
            self.apply_sparse_mds(config, region, offset, sparse_mds)?;
        }

        let constants = &spec.constants().end();
        for constants in constants.iter() {
            self.sbox_full(config, region, offset, constants)?;
            self.apply_mds(config, region, offset, mds)?;
        }
        self.sbox_full(config, region, offset, &[F::zero(); T])?;
        self.apply_mds(config, region, offset, mds)?;
        Ok(())
    }

    fn absorb_with_pre_constants(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE],
        pre_constants: &[F; T],
    ) -> Result <(), Error> {
        let s0 = vec![(&self.state[0], F::one())];
        self.state[0] = config.sum_with_constant(
            region,
            &mut (),
            offset,
            s0, Some(pre_constants[0].clone())
        )?;

        for ((x, constant), input) in self
            .state
            .iter_mut()
            .skip(1)
            .zip(pre_constants.iter().skip(1))
            .zip(inputs.iter())
        {
            *x = config.sum_with_constant(
                region,
                &mut (),
                offset,
                vec![(x, F::one()), (input, F::one())],
                Some(*constant)
            )?;
        }
        Ok(())
    }

    fn apply_mds(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        mds: &[[F; T]; T]
    ) -> Result<(), Error> {
        let res = mds
            .iter()
            .map(|row| {
                let a = self
                    .state
                    .iter()
                    .zip(row.iter())
                    .map(|(e, word)| (e, *word))
                    .collect::<Vec<_>>();

                config.sum_with_constant(
                    region,
                    &mut (),
                    offset,
                    a,
                    None).unwrap()
            })
            .collect::<Vec<_>>();

        self.state = res.try_into().unwrap();
        Ok(())
    }

    fn apply_sparse_mds(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        mds: &SparseMDSMatrix<F, T, RATE>,
    ) -> Result<(), Error> {
        let a = self
            .state
            .iter()
            .zip(mds.row().iter())
            .map(|(e, word)| (e, *word))
            .collect::<Vec<_>>();

        let sum = config.sum_with_constant(
            region,
            &mut (),
            offset,
            a,
            None
        )?;

        let mut res = vec![sum];

        for (e, x) in mds.col_hat().iter().zip(self.state.iter().skip(1)) {
            let c = &self.state[0];
            let sum = config.sum_with_constant(
                    region,
                    &mut (),
                    offset,
                    vec![(c, *e), (&x, F::one())],
                    None
            )?;
            res.push(sum);
        }

        for (x, new_x) in self.state.iter_mut().zip(res.into_iter()) {
            *x = new_x
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;
    use crate::host::poseidon::RATE;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        PoseidonChip,
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
        poseidonconfig: CommonGateConfig,
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
               poseidonconfig: PoseidonChip::<Fr>::configure(meta),
               helperconfig: HelperChip::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let mut poseidonchip = PoseidonChip::<Fr>::construct(config.clone().poseidonconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "assign poseidon test",
                |mut region| {
                    let mut offset = 0;
                    let result = helperchip.assign_result(&mut region, &mut offset, &self.result)?;
                    let inputs = helperchip.assign_inputs(&mut region, &mut offset, &self.inputs.clone().try_into().unwrap())?;
                    let reset = helperchip.assign_reset(&mut region, &mut offset, true)?;
                    offset = 0;
                    poseidonchip.poseidon_state.initialize(&config.poseidonconfig, &mut region, &mut offset)?;
                    poseidonchip.assign_permute(
                        &mut region,
                        &mut offset,
                        &inputs,
                        &reset,
                        &result
                    )?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }


    #[test]
    fn test_poseidon_circuit_00() {
        let mut hasher = crate::host::poseidon::gen_hasher();
        let result = hasher.squeeze();
        let inputs = vec![Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()];
        let test_circuit = TestCircuit {inputs, result};
        println!("result is {:?}", result);
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
