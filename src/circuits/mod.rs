use std::marker::PhantomData;
use std::sync::Arc;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
    pairing::bls12_381::{G1Affine, G2Affine, G1, G2}
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::pairing::bls12_381::pairing;
use halo2_proofs::pairing::group::prime::PrimeCurveAffine;
use halo2_proofs::pairing::group::Group;
use std::rc::Rc;
use std::cell::RefCell;
use rand::rngs::OsRng;
use halo2ecc_s::assign::AssignedG2Affine;
use halo2ecc_s::assign::AssignedCondition;
use halo2ecc_s::circuit::fq12::Fq12ChipOps;
use halo2ecc_s::circuit::fq12::Fq2ChipOps;
use halo2ecc_s::circuit::base_chip::BaseChipOps;
use halo2ecc_s::circuit::pairing_chip::PairingChipOps;
use halo2ecc_s::circuit::ecc_chip::EccChipBaseOps;

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
    },
    context::{Context, Records, GeneralScalarEccContext},
};


#[derive(Clone)]
pub struct Bls381ChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
}


#[derive(Default, Clone)]
pub struct Bls381PairCircuit<N: FieldExt> {
    records: Records<N>,
}

impl<N: FieldExt> Circuit<N> for Bls381PairCircuit<N> {
    type Config = Bls381ChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<N>::configure(meta);
        Bls381ChipConfig {
            base_chip_config,
            range_chip_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let base_chip = BaseChip::new(config.base_chip_config);
        let range_chip = RangeChip::<N>::new(config.range_chip_config);

        range_chip.init_table(&mut layouter)?;

        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                self.records
                    .assign_all(&mut region, &base_chip, &range_chip)?;
                end_timer!(timer);
                Ok(())
            },
        )?;

        Ok(())
    }
}

pub fn get_circuit_on_bn256(ctx: Context<Fr>, k: u32) -> Bls381PairCircuit<Fr> {
    println!("offset {} {}", ctx.range_offset, ctx.base_offset);
    let circuit = Bls381PairCircuit::<Fr> {
        records: Arc::try_unwrap(ctx.records).unwrap().into_inner().unwrap(),
    };
    circuit

    /*
    let prover = match MockProver::run(k, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
    */
}


pub fn load_bls381_pair_circuit() -> Bls381PairCircuit<Fr> {

    let contex = Rc::new(RefCell::new(Context::new()));
    let mut ctx = GeneralScalarEccContext::<G1Affine, Fr>::new(contex);

    let a = G1::random(&mut OsRng).into();
    let b = G2Affine::from(G2::random(&mut OsRng));

    let ab0 = pairing(&a, &b);

    let bx = ctx.fq2_assign_constant((b.x.c0, b.x.c1));
    let by = ctx.fq2_assign_constant((b.y.c0, b.y.c1));
    let b = AssignedG2Affine::new(
        bx,
        by,
        AssignedCondition(ctx.native_ctx.borrow_mut().assign_constant(Fr::zero())),
    );

    let a = ctx.assign_point(&a.to_curve());

    let ab = ctx.pairing(&[(&a, &b)]);

    /*
    ctx.fq12_assert_eq(&ab0, &ab);

    run_circuit_on_bn256(ctx.into(), 22);
    */
    get_circuit_on_bn256(ctx.into(), 22)
}


