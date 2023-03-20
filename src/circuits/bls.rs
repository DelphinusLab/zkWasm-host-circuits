use std::marker::PhantomData;
use std::sync::Arc;
use halo2ecc_s::circuit::base_chip::BaseChipOps;
use halo2_proofs::{
    arithmetic::{FieldExt, BaseExt},
    circuit::{AssignedCell, Chip, Layouter, Region},
    plonk::{Advice, Fixed, Column, ConstraintSystem, Error},
    pairing::bls12_381::G1Affine
};
use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::Fr;
use halo2ecc_s::circuit::fq12::Fq12ChipOps;
use std::rc::Rc;
use std::cell::RefCell;

use halo2_proofs::pairing::bls12_381::Fq as Bls381Fq;
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::assign::{
    AssignedCondition,
    Cell as ContextCell, AssignedFq
};
use halo2ecc_s::circuit::{
    pairing_chip::PairingChipOps,
    ecc_chip::EccChipBaseOps,
};
use halo2ecc_s::assign::{
    AssignedPoint,
    AssignedG2Affine,
    AssignedFq12,
};

use crate::host::bls::BLSOP;

pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;
pub const BLS381GT_SIZE: usize = 96;

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
    },
    context::{Context, GeneralScalarEccContext},
};

use num_bigint::BigUint;
use std::ops::{Mul, AddAssign};

#[derive(Clone, Debug)]
pub struct Bls381ChipConfig {
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
    a:&Vec<AssignedCell<Fr, Fr>>, //G1 (4 * 2 + 1)
    start: usize
) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in start..start + 4 {
        let shift = BigUint::from(2 as u32).pow(108 * (i - start) as u32);
        bn.add_assign(fr_to_bn(a[i].value().unwrap()).mul(shift.clone()));
    }
    bn
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a:&Vec<AssignedCell<Fr, Fr>>, //G1 (4 * 2 + 1)
) -> AssignedPoint<G1Affine, Fr> {
    let x_bn = assigned_cells_to_bn381(a, 0);
    let y_bn = assigned_cells_to_bn381(a, 4);
    let is_identity = fr_to_bool(a[8].value().unwrap());
    let x = ctx.base_integer_chip().assign_w(&x_bn);
    let y = ctx.base_integer_chip().assign_w(&y_bn);
    AssignedPoint::new(
        x,
        y,
        AssignedCondition(ctx.native_ctx.borrow_mut().assign(
            if is_identity { Fr::one() } else { Fr::zero() }
        ))
    )
}

fn get_g2_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    b:&Vec<AssignedCell<Fr, Fr>>, //G2 (4 * 4 + 1)
) -> AssignedG2Affine<G1Affine, Fr> {
    let x1_bn = assigned_cells_to_bn381(b, 0);
    let x2_bn = assigned_cells_to_bn381(b, 4);
    let y1_bn = assigned_cells_to_bn381(b, 8);
    let y2_bn = assigned_cells_to_bn381(b, 12);
    let x1 = ctx.base_integer_chip().assign_w(&x1_bn);
    let x2 = ctx.base_integer_chip().assign_w(&x2_bn);
    let y1 = ctx.base_integer_chip().assign_w(&y1_bn);
    let y2 = ctx.base_integer_chip().assign_w(&y2_bn);
    let is_identity = fr_to_bool(b[16].value().unwrap());
    AssignedG2Affine::new(
        (x1, x2),
        (y1, y2),
        AssignedCondition(ctx.native_ctx.borrow_mut().assign(
            if is_identity { Fr::one() } else { Fr::zero() }
        ))
    )
}

fn get_cell_of_ctx(
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    cell: &ContextCell,
) -> AssignedCell<Fr, Fr> {
    cells[cell.region as usize][cell.col][cell.row].clone().unwrap()
}

fn enable_fq_permute(
    region: &mut Region<'_, Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fq: &AssignedFq<Bls381Fq, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> Result<(), Error> {
    for i in 0..4 {
        let limb = fq.limbs_le[i].cell;
        let limb_assigned = get_cell_of_ctx(cells, &limb);
        region.constrain_equal(input[i].cell(), limb_assigned.cell())?;
    }
    Ok(())
}

fn enable_g1affine_permute(
    region: &mut Region<'_, Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedPoint<G1Affine, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, cells, &point.x, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y, &inputs.next().unwrap().to_vec())?;
    let z_limb0 = point.z.0.cell;
    let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    region.constrain_equal(input[8].cell(), z_limb0_assigned.cell())?;
    Ok(())
}

fn enable_g2affine_permute(
    region: &mut Region<'_, Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedG2Affine<G1Affine, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, cells, &point.x.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.x.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y.1, &inputs.next().unwrap().to_vec())?;
    let z_limb0 = point.z.0.cell;
    let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    region.constrain_equal(input[16].cell(), z_limb0_assigned.cell())?;
    Ok(())
}

fn enable_fq12_permute(
    region: &mut Region<'_, Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fq12: &AssignedFq12<Bls381Fq, Fr>,
    input: &Vec<AssignedCell<Fr, Fr>>
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, cells, &fq12.0.0.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.0.0.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.0.1.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.0.1.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.0.2.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.0.2.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.0.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.0.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.1.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.1.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.2.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &fq12.1.2.1, &inputs.next().unwrap().to_vec())?;
    Ok(())
}

impl Bls381PairChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        _meta: &mut ConstraintSystem<Fr>,
        _base_chip_config: BaseChipConfig,
        _range_chip_config: RangeChipConfig,
    ) -> <Self as Chip<Fr>>::Config {
        Bls381ChipConfig {}
    }

    pub fn load_bls381_pair_circuit(
        &self,
        a: &Vec<AssignedCell<Fr, Fr>>, //G1 (4 * 2 + 1)
        b: &Vec<AssignedCell<Fr, Fr>>, //G2 (4 * 4 + 1)
        ab: &Vec<AssignedCell<Fr, Fr>>, // Fq_12 (4 * 12)
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let contex = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::<G1Affine, Fr>::new(contex);

        let a_g1 = get_g1_from_cells(&mut ctx, a);
        let b_g2 = get_g2_from_cells(&mut ctx, b);

        let ab_fq12_raw = ctx.pairing(&[(&a_g1, &b_g2)]);
        let ab_fq12 = ctx.fq12_reduce(&ab_fq12_raw);

        let records = Arc::try_unwrap(Into::<Context<Fr>>::into(ctx).records).unwrap().into_inner().unwrap();

        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let cells = records
                    .assign_all(&mut region, &base_chip, &range_chip)?;
                enable_g1affine_permute(&mut region, &cells, &a_g1, a)?;
                enable_g2affine_permute(&mut region, &cells, &b_g2, b)?;
                enable_fq12_permute(&mut region, &cells, &ab_fq12, ab)?;
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    }
}

impl super::HostOpSelector for Bls381PairChip<Fr> {
    type Config = Bls381ChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        base_config: &BaseChipConfig,
        range_config: &RangeChipConfig
    ) -> Self::Config {
        Bls381PairChip::<Fr>::configure(
            meta,
            base_config.clone(),
            range_config.clone()
        )
    }

    fn construct(c: Self::Config) -> Self {
        Bls381PairChip::construct(c)
    }
    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(BLSOP::BLSPAIRG1 as u64),
            Fr::from(BLSOP::BLSPAIRG2 as u64),
            Fr::from(BLSOP::BLSPAIRGT as u64),
        ];
        let mut arg_cells = vec![];
        /* The 0,2,4,6's u54 of every Fq(8 * u54) return true, others false  */
        let merge_next = |i: usize| {
            let mut r = i % BLS381FQ_SIZE;
            if i >= BLS381G1_SIZE - 1 {
                r += BLS381FQ_SIZE - 1;
            }
            if i >= BLS381G1_SIZE + BLS381G2_SIZE - 1 {
                r += BLS381FQ_SIZE - 1;
            }
            r %= BLS381FQ_SIZE;
            r % 2 == 0
        };
        let mut offset = 0;
        let mut picked_offset = 0;
        let mut toggle: i32 = -1;
        for opcode in shared_opcodes {
            if opcodes.contains(opcode) {
                region.assign_advice(
                    || "picked operands",
                    filtered_operands,
                    picked_offset,
                    || Ok(shared_operands[offset])
                )?;

                region.assign_advice(
                    || "picked opcodes",
                    filtered_opcodes,
                    picked_offset,
                    || Ok(opcode.clone())
                )?;

                region.assign_advice(
                    || "picked index",
                    filtered_index,
                    picked_offset,
                    || Ok(shared_index[offset])
                )?;

                let value = if toggle >= 0 {
                    shared_operands[offset].clone().mul(&Fr::from(1u64 << 54)).add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };
                let opcell = region.assign_advice(
                    || "picked merged operands",
                    merged_operands,
                    picked_offset,
                    || Ok(value)
                )?;

                let value = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::one()
                } else {
                    arg_cells.append(&mut vec![opcell]);
                    toggle = -1;
                    Fr::zero()
                };
                region.assign_fixed(
                    || "indicator",
                    indicator,
                    picked_offset,
                    || Ok(value)
                )?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
    }
    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let a = arg_cells[0..9].to_vec();
        let b = arg_cells[9..26].to_vec();
        let ab = arg_cells[26..74].to_vec();
        self.load_bls381_pair_circuit(&a, &b, &ab, &base_chip, &range_chip, layouter)?;
        Ok(())
    }

}

#[derive(Clone, Debug)]
pub struct Bls381SumChip<N: FieldExt> {
    config: Bls381ChipConfig,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bls381SumChip<N> {
    type Config = Bls381ChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Bls381SumChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        _meta: &mut ConstraintSystem<Fr>,
        _base_chip_config: BaseChipConfig,
        _range_chip_config: RangeChipConfig,
    ) -> <Self as Chip<Fr>>::Config {
        Bls381ChipConfig {}
    }

    pub fn load_bls381_sum_circuit(
        &self,
        ls: &Vec<AssignedCell<Fr, Fr>>, // Vec<G1> (4 * 2 + 1) * k
        sum: &Vec<AssignedCell<Fr, Fr>>, // G1 (4 * 2 + 1)
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let contex = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::<G1Affine, Fr>::new(contex);

        let mut g1s:Vec<AssignedPoint<_, _>> = ls.chunks(9).map(|l| {
            get_g1_from_cells(&mut ctx, &l.to_vec())
        }).collect();

        let g0 = ctx.assign_identity();
        let sum_ret = g1s.iter().fold(g0, |acc, x| {
            let p = ctx.ecc_add(&acc, &x);
            ctx.to_point_with_curvature(p)
        });
        let sum_ret = sum_ret.to_point();
        ctx.native_ctx.borrow_mut().enable_permute(&sum_ret.z.0);
        let records = Arc::try_unwrap(Into::<Context<Fr>>::into(ctx).records).unwrap().into_inner().unwrap();
        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let cells = records
                    .assign_all(&mut region, &base_chip, &range_chip)?;
                let ls = ls.chunks(9)
                    .into_iter()
                    .map(|x| x.to_vec())
                    .collect::<Vec<_>>();
                g1s.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(&mut region, &cells, x, &ls[i]).unwrap()
                });
                enable_g1affine_permute(&mut region, &cells, &sum_ret, sum)?;
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    }
}

impl super::HostOpSelector for Bls381SumChip<Fr> {
    type Config = Bls381ChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        base_config: &BaseChipConfig,
        range_config: &RangeChipConfig
    ) -> Self::Config {
        Bls381SumChip::<Fr>::configure(
            meta,
            base_config.clone(),
            range_config.clone()
        )
    }

    fn construct(c: Self::Config) -> Self {
        Bls381SumChip::construct(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(BLSOP::BLSADD as u64),
            Fr::from(BLSOP::BLSSUM as u64),
        ];
        let mut arg_cells = vec![];
        /* The 0,2,4,6,8,10,12,14's u54 of every G1(17 * u54) return true, others false  */
        let merge_next = |i: usize| {
            let r = i % BLS381G1_SIZE;
            r % 2 == 0 && r != BLS381G1_SIZE - 1
        };
        let mut offset = 0;
        let mut picked_offset = 0;
        let mut toggle: i32 = -1;
        for opcode in shared_opcodes {
            if opcodes.contains(opcode) {
                region.assign_advice(
                    || "picked operands",
                    filtered_operands,
                    picked_offset,
                    || Ok(shared_operands[offset])
                )?;

                region.assign_advice(
                    || "picked opcodes",
                    filtered_opcodes,
                    picked_offset,
                    || Ok(opcode.clone())
                )?;

                region.assign_advice(
                    || "picked index",
                    filtered_index,
                    picked_offset,
                    || Ok(shared_index[offset])
                )?;

                let value = if toggle >= 0 {
                    shared_operands[offset].clone().mul(&Fr::from(1u64 << 54)).add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };
                let opcell = region.assign_advice(
                    || "picked merged operands",
                    merged_operands,
                    picked_offset,
                    || Ok(value)
                )?;

                let value = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::one()
                } else {
                    arg_cells.append(&mut vec![opcell]);
                    toggle = -1;
                    Fr::zero()
                };
                region.assign_fixed(
                    || "indicator",
                    indicator,
                    picked_offset,
                    || Ok(value)
                )?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
    }

    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let len = arg_cells.len();
        let args = arg_cells[0..len - 9].to_vec();
        let ret = arg_cells[len - 9..len].to_vec();
        self.load_bls381_sum_circuit(&args, &ret, &base_chip, &range_chip, layouter)?;
        Ok(())
    }
}


