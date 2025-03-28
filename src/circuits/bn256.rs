use ark_std::{end_timer, start_timer};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{Chip, Layouter, Region},
    pairing::bn256::G1Affine,
    plonk::{ConstraintSystem, Error},
};
use halo2ecc_o::circuit::assign::AssignedValue;
use halo2ecc_o::circuit::chips::pairing_chip::fq::Fq12ChipOps;

use std::marker::PhantomData;

use halo2_proofs::pairing::bn256::Fq as Bn256Fq;
use halo2ecc_o::circuit::assign::AssignedFq;
use halo2ecc_o::circuit::chips::{
    ecc_chip::EccChipBaseOps, msm_chip::EccChipMSMOps, native_chip::NativeChipOps,
    pairing_chip::PairingChipOps,
};

use halo2ecc_o::circuit::assign::{AssignedFq12, AssignedG2Affine, AssignedPoint};

use halo2ecc_o::{circuit::NativeScalarEccConfig, context::NativeScalarEccContext};

use crate::utils::Limb;
use num_bigint::BigUint;
use std::ops::{AddAssign, Mul};

#[derive(Clone, Debug)]
pub struct Bn256ChipConfig {
    ecc_chip_config: NativeScalarEccConfig,
}

pub struct Bn256PairChip<N: FieldExt> {
    config: Bn256ChipConfig,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bn256PairChip<N> {
    type Config = Bn256ChipConfig;
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

fn assigned_cells_to_bn256(
    a: &Vec<Limb<Fr>>, //G1 (3 * 2 + 1)
    start: usize,
) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in start..start + 3 {
        let shift = BigUint::from(2 as u32).pow(108 * (i - start) as u32);
        bn.add_assign(fr_to_bn(&a[i].value).mul(shift.clone()));
    }
    bn
}

fn assign_scalar(ctx: &mut NativeScalarEccContext<G1Affine>, a: Fr) -> AssignedValue<Fr> {
    ctx.plonk_region_context().assign(a).unwrap()
}

fn assign_point_g1(
    ctx: &mut NativeScalarEccContext<G1Affine>,
    a: &Vec<Limb<Fr>>, //G1 (3 * 2 + 1)
) -> AssignedPoint<G1Affine, Fr> {
    let x_bn = assigned_cells_to_bn256(a, 0);
    let y_bn = assigned_cells_to_bn256(a, 3);
    let is_identity = fr_to_bool(&a[6].value);
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

fn assign_point_g2(
    ctx: &mut NativeScalarEccContext<G1Affine>,
    b: &Vec<Limb<Fr>>, //G2 (3 * 4 + 1)
) -> AssignedG2Affine<G1Affine, Fr> {
    let x1_bn = assigned_cells_to_bn256(b, 0);
    let x2_bn = assigned_cells_to_bn256(b, 3);
    let y1_bn = assigned_cells_to_bn256(b, 6);
    let y2_bn = assigned_cells_to_bn256(b, 9);
    let x1 = ctx.integer_context().assign_w(Some(x1_bn)).unwrap();
    let x2 = ctx.integer_context().assign_w(Some(x2_bn)).unwrap();
    let y1 = ctx.integer_context().assign_w(Some(y1_bn)).unwrap();
    let y2 = ctx.integer_context().assign_w(Some(y2_bn)).unwrap();
    let is_identity = fr_to_bool(&b[12].value);
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
    region: &Region<Fr>,
    fr: &AssignedValue<Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    region.constrain_equal(input[0].get_the_cell().cell(), fr.cell())
}

fn enable_fq_permute(
    region: &Region<Fr>,
    fq: &AssignedFq<Bn256Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..3 {
        region.constrain_equal(
            input[i].get_the_cell().cell(),
            fq.limbs()[i].unwrap().cell(),
        )?;
    }
    Ok(())
}

fn enable_g1affine_permute(
    region: &Region<Fr>,
    point: &AssignedPoint<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
    enable_fq_permute(region, &point.x, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y, &inputs.next().unwrap().to_vec())?;
    region.constrain_equal(input[6].get_the_cell().cell(), point.z.cell())?;
    Ok(())
}

fn enable_g2affine_permute(
    region: &Region<Fr>,
    point: &AssignedG2Affine<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
    enable_fq_permute(region, &point.x.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.x.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, &point.y.1, &inputs.next().unwrap().to_vec())?;
    region.constrain_equal(input[12].get_the_cell().cell(), point.z.cell())?;
    Ok(())
}

fn enable_fq12_permute(
    region: &Region<Fr>,
    fq12: &AssignedFq12<Bn256Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
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

impl Bn256PairChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bn256ChipConfig {
            ecc_chip_config: NativeScalarEccConfig::configure::<G1Affine>(cs),
        }
    }

    pub fn load_bn256_pair_circuit(
        &self,
        a: &Vec<Limb<Fr>>,  //G1 (3 * 2 + 1)
        b: &Vec<Limb<Fr>>,  //G2 (3 * 4 + 1)
        ab: &Vec<Limb<Fr>>, // Fq_12 (3 * 12)
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "base",
            |region| {
                let timer = start_timer!(|| "assign");

                let mut ctx = self.config.ecc_chip_config.to_context(region);
                let a_g1 = assign_point_g1(&mut ctx, a);
                let b_g2 = assign_point_g2(&mut ctx, b);
                let ab_fq12_raw = ctx.pairing(&[(&a_g1, &b_g2)])?;
                let ab_fq12 = ctx.fq12_reduce(&ab_fq12_raw)?;

                enable_g1affine_permute(region, &a_g1, a)?;
                enable_g2affine_permute(region, &b_g2, b)?;
                enable_fq12_permute(region, &ab_fq12, ab)?;
                end_timer!(timer);

                let timer = start_timer!(|| "finalize int mul");
                ctx.integer_context().finalize_int_mul()?;
                end_timer!(timer);

                ctx.get_range_region_context().init()?;
                let timer = start_timer!(|| "finalize compact cells");
                ctx.get_range_region_context().finalize_compact_cells()?;
                end_timer!(timer);

                Ok(())
            },
        )?;
        Ok(())
    }
}

pub struct Bn256SumChip<N: FieldExt> {
    config: Bn256ChipConfig,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bn256SumChip<N> {
    type Config = Bn256ChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Bn256SumChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config: config.clone(),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bn256ChipConfig {
            ecc_chip_config: NativeScalarEccConfig::configure::<G1Affine>(cs),
        }
    }

    pub fn load_bn256_sum_circuit(
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
                let identity = ctx.assign_identity()?;
                let mut sum = identity.clone();
                for group in ls.chunks_exact(16) {
                    // using constraint to fix if to reset
                    let lhs = if group.get(0).unwrap().value != Fr::zero() {
                        identity.clone()
                    } else {
                        sum
                    };
                    let a = assign_scalar(&mut ctx, group.get(1).unwrap().value);
                    let g = assign_point_g1(&mut ctx, &group.get(2..9).unwrap().to_vec());
                    let rhs = ctx.ecc_mul(&g, a);
                    let sum_ret = ctx.ecc_add(&lhs, &rhs)?;
                    let sum_ret = ctx.ecc_reduce(&sum_ret)?;

                    sum = sum_ret.clone();
                    ais.push(a);
                    g1s.push(g);
                    sums.push(sum_ret);
                }

                ais.iter().enumerate().for_each(|(i, x)| {
                    enable_fr_permute(&mut region, x, &ls[16 * i + 1..16 * i + 2].to_vec()).unwrap()
                });
                g1s.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(&mut region, x, &ls[16 * i + 2..16 * i + 9].to_vec())
                        .unwrap()
                });
                sums.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(&mut region, x, &ls[16 * i + 9..16 * i + 16].to_vec())
                        .unwrap()
                });
                end_timer!(timer);

                let timer = start_timer!(|| "finalize int mul");
                ctx.integer_context().finalize_int_mul()?;
                end_timer!(timer);

                ctx.get_range_region_context().init()?;
                let timer = start_timer!(|| "finalize compact cells");
                ctx.get_range_region_context().finalize_compact_cells()?;
                end_timer!(timer);

                Ok(())
            },
        )?;
        Ok(())
    }
}
