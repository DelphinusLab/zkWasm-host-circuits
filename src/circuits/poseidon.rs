use crate::host::poseidon::PREFIX_CHALLENGE;
use crate::host::poseidon::PREFIX_POINT;
use crate::host::poseidon::PREFIX_SCALAR;
use crate::host::poseidon::RATE;
use crate::host::poseidon::R_F;
use crate::host::poseidon::R_P;
use crate::host::poseidon::T;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::FieldExt;
use poseidon::SparseMDSMatrix;
use poseidon::Spec;
use std::cell::RefMut;


use crate::circuits::{
    CommonGateConfig,
    Limb,
    range::{
       RangeCheckConfig,
       RangeCheckChip,
    }
};
use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Region, AssignedCell, Layouter},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
};

pub struct PoseidonState<F: FieldExt> {
    state: [Limb<F>; T],
    default: [Limb<F>; T],
    prefix: Vec<Limb<F>>,
}

pub struct PoseidonChip<F:FieldExt> {
    config: CommonGateConfig,
    spec: Spec<F, T, RATE>,
    poseidon_state: PoseidonState<F>,
    round: u32,
    _marker: PhantomData<F>
}

impl<F: FieldExt> PoseidonChip<F> {
    pub fn new(config: CommonGateConfig) -> Self {
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

    pub fn configure(cs: &mut ConstraintSystem<F>, range_check_config: &RangeCheckConfig) -> CommonGateConfig {
        CommonGateConfig::configure(cs, range_check_config)
    }

    pub fn assign_permute(
        &mut self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        values: &[F; RATE],
        create: bool,
        squeeze: bool,
    ) -> Result<(), Error> {
        let mut new_state = vec![];
        let create_limb = Limb::new(None, if create {F::one()} else {F::zero()});
        for (value, default) in self.poseidon_state.state.iter().zip(self.poseidon_state.default.iter()) {
            new_state.push(self.config.select(region, range_check_chip, offset, &create_limb, default, value)?);
        }
        self.poseidon_state.state = new_state.try_into().unwrap();
        let parts = values.clone().map(|x| {Some(Limb::new(None, x.clone()))});
        let parts = parts.chunks(4).collect::<Vec<_>>();
        let mut part0 = parts[0].to_vec();
        let mut part1 = parts[1].to_vec();
        part0.push(None);
        part1.push(None);
        let mut inputs = self.config.assign_witness(
            region,
            range_check_chip,
            offset,
            part0.try_into().unwrap(),
            0,
        )?;
        inputs.append(&mut self.config.assign_witness(
            region,
            range_check_chip,
            offset,
            part1.try_into().unwrap(),
            0,
        )?);
        self.poseidon_state.permute(
            &self.config,
            &self.spec,
            region,
            range_check_chip,
            offset,
            &inputs.try_into().unwrap(),
        )?;
        // register the result with squeeze and create indicator
        self.config.assign_witness(
            region,
            range_check_chip,
            offset,
            [
                Some(self.poseidon_state.state[0].clone()),
                Some(Limb::new(None, if squeeze {F::one()} else {F::zero()})),
                Some(create_limb),
                None,
                None
            ],
            1 // Need to do the lookup check of squeeze
        )?;
        Ok(())
    }
}

impl<F: FieldExt> PoseidonState<F> {
    pub fn init(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero = config.assign_constant(region, range_check_chip, offset, &F::zero())?;
        let mut state = [0u32;T].map(|_| zero.clone());
        state[0] = config.assign_constant(region, range_check_chip, offset, &F::from_u128(1u128<<64))?;
        self.default = state.clone();
        self.state = state;
        self.prefix = vec![
                config.assign_constant(region, range_check_chip, offset, &F::from(PREFIX_CHALLENGE))?,
                config.assign_constant(region, range_check_chip, offset, &F::from(PREFIX_POINT))?,
                config.assign_constant(region, range_check_chip, offset, &F::from(PREFIX_SCALAR))?,
            ];
        Ok(())
    }

    fn x_power5_with_constant(
        config: &CommonGateConfig,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        x: &Limb<F>,
        constant: F,
    ) -> Result<Limb<F>, Error> {
        let xx = config.assign_line(region, range_check_chip, offset,
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
        let x4 = config.assign_line(region, range_check_chip, offset,
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
        let x5 = config.assign_line(region, range_check_chip, offset,
            [
                Some(x.clone()),
                None,
                None,
                Some(x4.clone()),
                Some(Limb::new(None, x4.value * x.value)),
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
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        constants: &[F; T]
    ) -> Result<(), Error> {
        for (x, constant) in self.state.iter_mut().zip(constants.iter()) {
            *x = Self::x_power5_with_constant(config, region, range_check_chip, offset, x, *constant)?;
        }
        Ok(())
    }

    fn sbox_part(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        constant: &F
    ) -> Result<(), Error> {
        self.state[0] = Self::x_power5_with_constant(
            config,
            region,
            range_check_chip,
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
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE],
    ) -> Result<(), Error> {
        let r_f = R_F / 2;
        let mds = &spec.mds_matrices().mds().rows();

        let constants = &spec.constants().start();
        self.absorb_with_pre_constants(config, region, range_check_chip, offset, inputs, &constants[0])?;

        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.sbox_full(config, region, range_check_chip, offset, constants)?;
            self.apply_mds(config, region, range_check_chip, offset, mds)?;
        }

        let pre_sparse_mds = &spec.mds_matrices().pre_sparse_mds().rows();
        self.sbox_full(config, region, range_check_chip, offset,constants.last().unwrap())?;
        self.apply_mds(config, region, range_check_chip, offset, &pre_sparse_mds)?;

        let sparse_matrices = &spec.mds_matrices().sparse_matrices();
        let constants = &spec.constants().partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.sbox_part(config, region, range_check_chip, offset, constant)?;
            self.apply_sparse_mds(config, region, range_check_chip, offset, sparse_mds)?;
        }

        let constants = &spec.constants().end();
        for constants in constants.iter() {
            self.sbox_full(config, region, range_check_chip, offset, constants)?;
            self.apply_mds(config, region, range_check_chip, offset, mds)?;
        }
        self.sbox_full(config, region, range_check_chip, offset, &[F::zero(); T])?;
        self.apply_mds(config, region, range_check_chip, offset, mds)?;
        Ok(())
    }

    fn absorb_with_pre_constants(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE],
        pre_constants: &[F; T],
    ) -> Result <(), Error> {
        let s0 = vec![(&self.state[0], F::one())];
        self.state[0] = config.sum_with_constant(
            region,
            range_check_chip,
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
                range_check_chip,
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
        range_check_chip: &mut RangeCheckChip<F>,
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
                    range_check_chip,
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
        range_check_chip: &mut RangeCheckChip<F>,
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
            range_check_chip,
            offset,
            a,
            None
        )?;

        let mut res = vec![sum];

        for (e, x) in mds.col_hat().iter().zip(self.state.iter().skip(1)) {
            let c = &self.state[0];
            let sum = config.sum_with_constant(
                    region,
                    range_check_chip,
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

/*
impl<F: FieldExt> PoseidonState<F> {
    pub fn update(
        &mut self,
        chip: &mut RefMut<'_, dyn BaseChipOps<F>>,
        mut inputs: Vec<AssignedValue<F>>,
    ) {
        self.absorbing.append(&mut inputs);

        if self.absorbing.len() < RATE {
            return;
        }

        let mut values = vec![];
        values.append(&mut self.absorbing);

        for chunk in values.chunks(RATE) {
            if chunk.len() < RATE {
                self.absorbing = chunk.to_vec();
            } else {
                self.permute(chip, &chunk, false);
            }
        }
    }

    pub fn squeeze(&mut self, chip: &mut RefMut<'_, dyn BaseChipOps<F>>) -> AssignedValue<F> {
        assert!(self.absorbing.len() < RATE);

        let mut values = vec![];
        values.append(&mut self.absorbing);

        self.permute(chip, &values, true);

        self.state.0[1]
    }

}
*/
