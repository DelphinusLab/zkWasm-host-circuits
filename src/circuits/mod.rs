use std::{marker::PhantomData, ops::Add};
use std::sync::Arc;
use halo2ecc_s::circuit::ecc_chip::EccChipBaseOps;
use subtle::Choice;
use halo2_proofs::arithmetic::{BaseExt, CurveAffine};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
    pairing::bls12_381::{G1Affine, G2Affine, G1, G2 }
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::Fr;
use std::rc::Rc;
use std::cell::RefCell;

use halo2_proofs::pairing::bls12_381::pairing;
use halo2_proofs::pairing::bls12_381::Fq as Bls381Fq;
/*
use halo2ecc_s::{assign::AssignedG2Affine, circuit::ecc_chip::EccBaseIntegerChipWrapper};
use halo2ecc_s::assign::AssignedCondition;
use halo2ecc_s::circuit::fq12::Fq12ChipOps;
use halo2ecc_s::circuit::fq12::Fq2ChipOps;
use halo2ecc_s::circuit::base_chip::BaseChipOps;
use halo2ecc_s::circuit::ecc_chip::EccChipBaseOps;
use halo2_proofs::pairing::group::prime::PrimeCurveAffine;
use halo2_proofs::pairing::group::Group;
*/
use halo2ecc_s::circuit::pairing_chip::PairingChipOps;
use halo2ecc_s::assign::{
    AssignedPoint,
    AssignedG2Affine,
    AssignedFq12,
};

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
    },
    context::{Context, Records, GeneralScalarEccContext},
};

use crate::utils::{field_to_bn, bn_to_field};
use num_bigint::BigUint;
use std::ops::{Mul, AddAssign};


#[derive(Clone, Debug)]
pub struct Bls381ChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
}


#[derive(Clone, Debug)]
pub struct Bls381PairChip<N: FieldExt> {
    config: Bls381ChipConfig,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bls381PairChip<N> {
    type Config = Bls381ChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

pub fn fr_to_bn(f: &Fr) -> BigUint {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    BigUint::from_bytes_le(&bytes[..])
}

pub fn fr_to_bool(f: &Fr) -> bool {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    return bytes[0] == 1u8;
}

fn assigned_cells_to_bn381 (
    a:&Vec<AssignedCell<Fr, Fr>>, //G1 (5 * 2 + 1)
    start: usize
) -> BigUint {
    let shift = BigUint::from(2 as u32).pow(90);
    let mut bn = BigUint::from(0 as u64);
    for i in start..start+5 {
        bn.add_assign(fr_to_bn(a[i].value().unwrap()).mul(shift.clone()));
    }
    bn
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a:&Vec<AssignedCell<Fr, Fr>>, //G1 (5 * 2 + 1)
) -> AssignedPoint<G1Affine, Fr> {
    let x_bn = assigned_cells_to_bn381(a, 0);
    let y_bn = assigned_cells_to_bn381(a, 5);

    let is_identity = fr_to_bool(a[10].value().unwrap());

    let a = if is_identity {
        G1::identity()
    } else {
        G1::from(G1Affine::from_xy(
            bn_to_field(&x_bn),
            bn_to_field(&y_bn)
        ).unwrap())
    };

    ctx.assign_point(&a)
}

fn get_g2_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    b:&Vec<AssignedCell<Fr, Fr>>, //G1 (5 * 2 + 1)
) -> AssignedG2Affine<G1Affine, Fr> {
    let x1_bn = assigned_cells_to_bn381(b, 0);
    let x2_bn = assigned_cells_to_bn381(b, 5);
    let y_bn = assigned_cells_to_bn381(b, 10);
    let y2_bn = assigned_cells_to_bn381(b, 15);
    todo!()
}

fn enable_g1affine_permute(
    region: &mut Region<'_, Fr>,
    records: &mut Records<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedPoint<G1Affine, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> () {
    todo!()

}

fn enable_g2affine_permute(
    region: &mut Region<'_, Fr>,
    records: &mut Records<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedG2Affine<G1Affine, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> () {
    todo!()
}


fn enable_fq12_permute(
    region: &mut Region<'_, Fr>,
    records: &mut Records<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fq12: &AssignedFq12<Bls381Fq, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> () {
    //region.constrain_equal(assigned_cell.cell(), self.cell())?;

}


impl Bls381PairChip<Fr> {
    fn construct(config: <Self as Chip<Fr>>::Config, _loaded: <Self as Chip<Fr>>::Loaded) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> <Self as Chip<Fr>>::Config {
        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<Fr>::configure(meta);
        Bls381ChipConfig {
            base_chip_config,
            range_chip_config,
        }
    }

    pub fn load_bls381_pair_circuit(
        &self,
        a: &Vec<AssignedCell<Fr, Fr>>, //G1 (5 * 2 + 1)
        b: &Vec<AssignedCell<Fr, Fr>>, //G2 (10 * 2 + 1)
        ab: &Vec<AssignedCell<Fr, Fr>>, // Fq_12 (5*12)
        base_chip: BaseChip<Fr>,
        range_chip: RangeChip<Fr>,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let contex = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::<G1Affine, Fr>::new(contex);

        /* FIXME: Calculate a b from input vec_a and vec_b */

        //let a = G1::random(&mut OsRng).into();
        //let b = G2Affine::from(G2::random(&mut OsRng));

        //let ab0 = pairing(&a, &b);
        //
        //
        let a_g1 = get_g1_from_cells(&mut ctx, a);
        let b_g2 = get_g2_from_cells(&mut ctx, b);


        let ab_fq12 = ctx.pairing(&[(&a_g1, &b_g2)]);

        /*
        ctx.fq12_assert_eq(&ab0, &ab);

        run_circuit_on_bn256(ctx.into(), 22);
        */
        let mut records = Arc::try_unwrap(Into::<Context<Fr>>::into(ctx).records).unwrap().into_inner().unwrap();

        //records.enable_permute(&ab.0.0.0.limbs_le[0].cell);

        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let cells = records
                    .assign_all(&mut region, &base_chip, &range_chip)?;
                enable_g1affine_permute(&mut region, &mut records, &cells, &a_g1, a);
                enable_g2affine_permute(&mut region, &mut records, &cells, &b_g2, b);
                enable_fq12_permute(&mut region, &mut records, &cells, &ab_fq12, ab);
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    }

}
