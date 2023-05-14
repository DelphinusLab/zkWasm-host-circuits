use crate::host::poseidon::PREFIX_CHALLENGE;
use crate::host::poseidon::PREFIX_POINT;
use crate::host::poseidon::PREFIX_SCALAR;
use crate::host::poseidon::RATE;
use crate::host::poseidon::R_F;
use crate::host::poseidon::R_P;
use crate::host::poseidon::T;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::arithmetic::FieldExt;
use halo2ecc_s::assign::AssignedValue;
use halo2ecc_s::circuit::base_chip::BaseChipOps;
use halo2ecc_s::context::NativeScalarEccContext;
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use poseidon::SparseMDSMatrix;
use poseidon::Spec;
use std::cell::RefMut;

pub struct PoseidonChipRead<C: CurveAffine> {
    state: PoseidonChipContext<C::ScalarExt>,
    prefix: Vec<AssignedValue<C::ScalarExt>>,
}

impl<C: CurveAffine> PoseidonChipRead<C> {
    pub fn init(
        circuit: &mut NativeScalarEccContext<C>,
    ) -> Self {
        let state = PoseidonChipContext::new(&mut circuit.base_integer_chip().base_chip());
        let base_chip = &mut circuit.base_integer_chip().base_chip();
        Self {
            state,
            prefix: vec![
                base_chip.assign_constant(C::ScalarExt::from(PREFIX_CHALLENGE)),
                base_chip.assign_constant(C::ScalarExt::from(PREFIX_POINT)),
                base_chip.assign_constant(C::ScalarExt::from(PREFIX_SCALAR)),
            ],
        }
    }

    pub fn squeeze(
        &mut self,
        circuit: &mut NativeScalarEccContext<C>,
    ) -> AssignedValue<C::ScalarExt> {
        self.state.update(
            &mut circuit.base_integer_chip().base_chip(),
            vec![self.prefix[0]],
        );
        self.state
            .squeeze(&mut circuit.base_integer_chip().base_chip())
    }
}

struct PoseidonChipState<F: FieldExt>([AssignedValue<F>; T]);

pub struct PoseidonChipContext<F: FieldExt> {
    spec: Spec<F, T, RATE>,
    state: PoseidonChipState<F>,
    absorbing: Vec<AssignedValue<F>>,
}

impl<F: FieldExt> PoseidonChipContext<F> {
    pub fn new(chip: &mut RefMut<'_, dyn BaseChipOps<F>>) -> Self {
        let zero = chip.assign_constant(F::zero());
        let mut state = [zero; T];
        state[0] = chip.assign_constant(F::from_u128(1u128 << 64));
        Self {
            spec: Spec::new(R_F, R_P),
            state: PoseidonChipState(state),
            absorbing: vec![],
        }
    }

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

    fn permute(
        &mut self,
        chip: &mut RefMut<'_, dyn BaseChipOps<F>>,
        inputs: &[AssignedValue<F>],
        on_squeeze: bool,
    ) {
        let r_f = R_F / 2;
        let mds = &self.spec.mds_matrices().mds().rows();

        let constants = &self.spec.constants().start();
        self.state
            .absorb_with_pre_constants(chip, inputs, &constants[0], on_squeeze);

        for constants in constants.iter().skip(1).take(r_f - 1) {
            self.state.sbox_full(chip, constants);
            self.state.apply_mds(chip, mds);
        }

        let pre_sparse_mds = &self.spec.mds_matrices().pre_sparse_mds().rows();
        self.state.sbox_full(chip, constants.last().unwrap());
        self.state.apply_mds(chip, &pre_sparse_mds);

        let sparse_matrices = &self.spec.mds_matrices().sparse_matrices();
        let constants = &self.spec.constants().partial();
        for (constant, sparse_mds) in constants.iter().zip(sparse_matrices.iter()) {
            self.state.sbox_part(chip, constant);
            self.state.apply_sparse_mds(chip, sparse_mds);
        }

        let constants = &self.spec.constants().end();
        for constants in constants.iter() {
            self.state.sbox_full(chip, constants);
            self.state.apply_mds(chip, mds);
        }
        self.state.sbox_full(chip, &[F::zero(); T]);
        self.state.apply_mds(chip, mds);
    }
}

impl<F: FieldExt> PoseidonChipState<F> {
    fn x_power5_with_constant(
        chip: &mut RefMut<'_, dyn BaseChipOps<F>>,
        x: &AssignedValue<F>,
        constant: F,
    ) -> AssignedValue<F> {
        let x2 = chip.mul(x, x);
        let x4 = chip.mul(&x2, &x2);
        chip.mul_add_constant(&x, &x4, constant)
    }

    fn sbox_full(&mut self, chip: &mut RefMut<'_, dyn BaseChipOps<F>>, constants: &[F; T]) {
        for (x, constant) in self.0.iter_mut().zip(constants.iter()) {
            *x = Self::x_power5_with_constant(chip, x, *constant);
        }
    }

    fn sbox_part(&mut self, chip: &mut RefMut<'_, dyn BaseChipOps<F>>, constant: &F) {
        self.0[0] = Self::x_power5_with_constant(chip, &self.0[0], constant.clone());
    }

    fn absorb_with_pre_constants(
        &mut self,
        chip: &mut RefMut<'_, dyn BaseChipOps<F>>,
        inputs: &[AssignedValue<F>],
        pre_constants: &[F; T],
        on_squeeze: bool,
    ) {
        assert!(inputs.len() < T);
        let zero = F::zero();
        let one = F::one();

        let offset = inputs.len() + 1;

        self.0[0] = chip.add_constant(&self.0[0], pre_constants[0]);

        for ((x, constant), input) in self
            .0
            .iter_mut()
            .skip(1)
            .zip(pre_constants.iter().skip(1))
            .zip(inputs.iter())
        {
            *x = chip.sum_with_constant(vec![(&x, one), (input, one)], Some(*constant));
        }

        for (i, (x, constant)) in self
            .0
            .iter_mut()
            .skip(offset)
            .zip(pre_constants.iter().skip(offset))
            .enumerate()
        {
            *x = chip.add_constant(x, *constant + if i == 0 && on_squeeze { one } else { zero });
        }
    }

    fn apply_mds(&mut self, chip: &mut RefMut<'_, dyn BaseChipOps<F>>, mds: &[[F; T]; T]) {
        let res = mds
            .iter()
            .map(|row| {
                let a = self
                    .0
                    .iter()
                    .zip(row.iter())
                    .map(|(e, word)| (e, *word))
                    .collect::<Vec<_>>();

                chip.sum_with_constant(a, None)
            })
            .collect::<Vec<_>>();

        self.0 = res.try_into().unwrap();
    }

    fn apply_sparse_mds(
        &mut self,
        chip: &mut RefMut<'_, dyn BaseChipOps<F>>,
        mds: &SparseMDSMatrix<F, T, RATE>,
    ) {
        let a = self
            .0
            .iter()
            .zip(mds.row().iter())
            .map(|(e, word)| (e, *word))
            .collect::<Vec<_>>();

        let mut res = vec![chip.sum_with_constant(a, None)];

        for (e, x) in mds.col_hat().iter().zip(self.0.iter().skip(1)) {
            res.push(chip.sum_with_constant(vec![(&self.0[0], *e), (&x, F::one())], None));
        }

        for (x, new_x) in self.0.iter_mut().zip(res.into_iter()) {
            *x = new_x
        }
    }
}
