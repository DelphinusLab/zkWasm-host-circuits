use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bls12_381::Fr as Scalar;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{Chip, Layouter, Region},
    pairing::bls12_381::G1Affine,
    plonk::{ConstraintSystem, Error},
};

use halo2ecc_o::circuit::chips::pairing_chip::fq::Fq12ChipOps;
use std::marker::PhantomData;

use halo2_proofs::pairing::bls12_381::Fq as Bls381Fq;
use halo2ecc_o::circuit::assign::{AssignedFq, AssignedInteger};
use halo2ecc_o::circuit::assign::{AssignedFq12, AssignedG2Affine, AssignedPoint};
use halo2ecc_o::circuit::chips::{
    ecc_chip::EccChipBaseOps, msm_chip::EccChipMSMOps, native_chip::NativeChipOps,
    pairing_chip::PairingChipOps,
};

pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;

use halo2ecc_o::context::GeneralScalarEccContext;
use halo2ecc_o::GeneralScalarEccConfig;

use crate::utils::Limb;
use num_bigint::BigUint;
use std::ops::{AddAssign, Mul};

#[derive(Clone, Debug)]
pub struct Bls381ChipConfig {
    ecc_chip_config: GeneralScalarEccConfig,
}

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

fn assigned_cells_to_fr(
    a: &Vec<Limb<Fr>>, //Fr (3)
    start: usize,
) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in start..start + 3 {
        let shift = BigUint::from(2 as u32).pow(108 * (i - start) as u32);
        bn.add_assign(fr_to_bn(&a[i].value).mul(shift.clone()));
    }
    bn
}

fn assigned_cells_to_bn381(
    a: &Vec<Limb<Fr>>, //G1 (4 * 2 + 1)
    start: usize,
) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in start..start + 4 {
        let shift = BigUint::from(2 as u32).pow(108 * (i - start) as u32);
        bn.add_assign(fr_to_bn(&a[i].value).mul(shift.clone()));
    }
    bn
}

fn get_scalar_from_cell(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<Limb<Fr>>,
) -> AssignedInteger<Scalar, Fr> {
    let bn = assigned_cells_to_fr(a, 0);
    let fr = ctx.scalar_integer_context().assign_w(Some(bn)).unwrap();
    fr
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<Limb<Fr>>, //G1 (4 * 2 + 1)
) -> AssignedPoint<G1Affine, Fr> {
    let x_bn = assigned_cells_to_bn381(a, 0);
    let y_bn = assigned_cells_to_bn381(a, 4);
    let is_identity = fr_to_bool(&a[8].value);
    let x = ctx.integer_context().assign_w(Some(x_bn)).unwrap();
    let y = ctx.integer_context().assign_w(Some(y_bn)).unwrap();
    AssignedPoint::new(
        x,
        y,
        ctx.plonk_region_context()
            .assign(if is_identity { Fr::one() } else { Fr::zero() })
            .unwrap()
            .into(),
    )
}

fn get_g2_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    b: &Vec<Limb<Fr>>, //G2 (4 * 4 + 1)
) -> AssignedG2Affine<G1Affine, Fr> {
    let x1_bn = assigned_cells_to_bn381(b, 0);
    let x2_bn = assigned_cells_to_bn381(b, 4);
    let y1_bn = assigned_cells_to_bn381(b, 8);
    let y2_bn = assigned_cells_to_bn381(b, 12);
    let x1 = ctx.integer_context().assign_w(Some(x1_bn)).unwrap();
    let x2 = ctx.integer_context().assign_w(Some(x2_bn)).unwrap();
    let y1 = ctx.integer_context().assign_w(Some(y1_bn)).unwrap();
    let y2 = ctx.integer_context().assign_w(Some(y2_bn)).unwrap();
    let is_identity = fr_to_bool(&b[16].value);
    AssignedG2Affine::new(
        (x1, x2),
        (y1, y2),
        ctx.plonk_region_context()
            .assign(if is_identity { Fr::one() } else { Fr::zero() })
            .unwrap()
            .into(),
    )
}

fn enable_fr_permute(
    region: &Region<'_, Fr>,
    fr: &AssignedInteger<Scalar, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..3 {
        region.constrain_equal(
            input[i].get_the_cell().cell(),
            fr.limbs()[i].unwrap().cell(),
        )?;
    }
    Ok(())
}

fn enable_fq_permute(
    region: &Region<'_, Fr>,
    fq: &AssignedFq<Bls381Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..4 {
        region.constrain_equal(
            input[i].get_the_cell().cell(),
            fq.limbs()[i].unwrap().cell(),
        )?;
    }
    Ok(())
}

fn enable_g1affine_permute(
    region: &Region<'_, Fr>,
    point: &AssignedPoint<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, &point.x, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y, &inputs.next().unwrap().to_vec())?;
    region.constrain_equal(input[8].get_the_cell().cell(), point.z.cell())?;
    Ok(())
}

fn enable_g2affine_permute(
    region: &Region<'_, Fr>,
    point: &AssignedG2Affine<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, &point.x.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.x.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y.1, &inputs.next().unwrap().to_vec())?;
    region.constrain_equal(input[16].get_the_cell().cell(), point.z.cell())?;
    Ok(())
}

fn enable_fq12_permute(
    region: &Region<'_, Fr>,
    fq12: &AssignedFq12<Bls381Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(4);
    enable_fq_permute(region, &fq12.0 .0 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.0 .0 .1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.0 .1 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.0 .1 .1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.0 .2 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.0 .2 .1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .0 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .0 .1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .1 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .1 .1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .2 .0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &fq12.1 .2 .1, &inputs.next().unwrap().to_vec())?;
    Ok(())
}

impl Bls381PairChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bls381ChipConfig {
            ecc_chip_config: GeneralScalarEccConfig::configure::<G1Affine, Fr>(cs),
        }
    }

    pub fn load_bls381_pair_circuit(
        &self,
        a: &Vec<Limb<Fr>>,  //G1 (4 * 2 + 1)
        b: &Vec<Limb<Fr>>,  //G2 (4 * 4 + 1)
        ab: &Vec<Limb<Fr>>, // Fq_12 (4 * 12)
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let mut ctx = self.config.ecc_chip_config.to_context(region);

                let a_g1 = get_g1_from_cells(&mut ctx, a);
                let b_g2 = get_g2_from_cells(&mut ctx, b);

                let ab_fq12_raw = ctx.pairing(&[(&a_g1, &b_g2)]).unwrap();
                let ab_fq12 = ctx.fq12_reduce(&ab_fq12_raw).unwrap();

                enable_g1affine_permute(&mut region, &a_g1, a)?;
                enable_g2affine_permute(&mut region, &b_g2, b)?;
                enable_fq12_permute(&mut region, &ab_fq12, ab)?;
                end_timer!(timer);

                let timer = start_timer!(|| "finalize int mul");
                ctx.integer_context().finalize_int_mul()?;
                ctx.scalar_integer_context().finalize_int_mul()?;
                end_timer!(timer);

                ctx.get_range_region_context().init()?;
                ctx.get_scalar_range_region_context().init()?;
                let timer = start_timer!(|| "finalize compact cells");
                ctx.get_range_region_context().finalize_compact_cells()?;
                ctx.get_scalar_range_region_context()
                    .finalize_compact_cells()?;
                end_timer!(timer);

                Ok(())
            },
        )?;
        Ok(())
    }
}

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
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bls381ChipConfig {
            ecc_chip_config: GeneralScalarEccConfig::configure::<G1Affine, Fr>(cs),
        }
    }

    pub fn load_bls381_sum_circuit(
        &self,
        ls: &Vec<Limb<Fr>>, // n * (new, fr , g1, sum)
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let mut ctx = self.config.ecc_chip_config.to_context(region);
                let mut ais = vec![];
                let mut g1s = vec![];
                let mut sums = vec![];
                let identity = ctx.assign_identity().unwrap();
                let mut sum = identity.clone();
                for group in ls.chunks_exact(22) {
                    // using constraint to fix if to reset
                    let lhs = if group.get(0).unwrap().value != Fr::zero() {
                        identity.clone()
                    } else {
                        sum
                    };
                    let a = get_scalar_from_cell(&mut ctx, &group.get(1..4).unwrap().to_vec());
                    ais.push(a.clone());
                    let g = get_g1_from_cells(&mut ctx, &group.get(4..13).unwrap().to_vec());
                    let rhs = ctx.ecc_mul(&g, a);
                    let sum_ret = ctx.ecc_add(&lhs, &rhs)?;
                    let sum_ret = ctx.ecc_reduce(&sum_ret)?;

                    sum = sum_ret.clone();
                    g1s.push(g);
                    sums.push(sum_ret);
                }

                ais.iter().enumerate().for_each(|(i, x)| {
                    enable_fr_permute(&mut region, x, &ls[22 * i + 1..22 * i + 4].to_vec()).unwrap()
                });
                g1s.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(&mut region, x, &ls[22 * i + 4..22 * i + 13].to_vec())
                        .unwrap()
                });
                sums.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(&mut region, x, &ls[22 * i + 13..22 * i + 22].to_vec())
                        .unwrap()
                });
                end_timer!(timer);

                let timer = start_timer!(|| "finalize int mul");
                ctx.integer_context().finalize_int_mul()?;
                ctx.scalar_integer_context().finalize_int_mul()?;
                end_timer!(timer);

                ctx.get_range_region_context().init()?;
                ctx.get_scalar_range_region_context().init()?;
                let timer = start_timer!(|| "finalize compact cells");
                ctx.get_range_region_context().finalize_compact_cells()?;
                ctx.get_scalar_range_region_context()
                    .finalize_compact_cells()?;
                end_timer!(timer);

                Ok(())
            },
        )?;
        Ok(())
    }
}
