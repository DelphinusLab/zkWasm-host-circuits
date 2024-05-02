use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::bls12_381::pairing;
use halo2_proofs::pairing::bls12_381::{G1Affine, G2Affine};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use crate::circuits::hash2G2::{Hash2CurveChip, Hash2CurveChipConfig};

use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::utils::Limb;

use super::get_selected_entries;
use crate::host::{ExternalHostCallEntry, ForeignInst};

pub const BLS381FR_SIZE: usize = 5; // 5 * 54 = 270
pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381FQ2_SIZE: usize = 16; // 8 * 2
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;

const HASH2CURVE_SIZE: usize = 2 * BLS381FQ2_SIZE + BLS381G2_SIZE; // u + output

// default representation of G2 in host

fn bls381_g2_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G2Affine::default();
    r.append(&mut crate::adaptor::fr_to_args(a.x.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.x.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.y.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.y.c1, 8, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: a.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bls381_fq2_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for _ in 0..BLS381FQ2_SIZE {
        r.push(ExternalHostCallEntry {
            op: op as usize,
            value: 0u64,
            is_ret: false,
        });
    }
    r
}

impl HostOpSelector for Hash2CurveChip<Fr> {
    type Config = Hash2CurveChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Hash2CurveChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Hash2CurveChip::construct(c)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::Hash2CurvePush as u64),
            Fr::from(ForeignInst::Hash2CurveResult as u64),
        ]
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, 1)
    }

    fn assign(
        region: &mut Region<Fr>,
        k: usize,
        _offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();

        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        //assert!(selected_entries.len() % BLSPAIR_SIZE == 0);
        let total_used_instructions = selected_entries.len() / HASH2CURVE_SIZE;

        let mut offset = 0;
        let mut r = vec![];

        // input: two Fq2 elements
        for group in selected_entries.chunks_exact(HASH2CURVE_SIZE) {
            for k in 0..2 {
                for i in 0..8 {
                    let (limb, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&group[2 * i + 16 * k], &group[ 2 * i + 16 * k + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(limb);
                }
            }

            // output: one G2 element
            for y in 0..2 {
                for i in 0..8 {
                    let (limb, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&group[32 + 2 * i + 16 * y], &group[32 + 2 * i + 16 * y + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                r.push(limb);
                }
            }

            let ((operand, opcode), index) = *group.get(32 + 32).clone().unwrap();

            let (limb, _) = config.assign_one_line(
                region,
                &mut offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                true,
            )?;
            r.push(limb);
        }

        // default table
        let mut default_table = vec![];

        default_table.append(&mut bls381_fq2_default(ForeignInst::Hash2CurvePush));
        default_table.append(&mut bls381_fq2_default(ForeignInst::Hash2CurvePush));
        default_table.append(&mut bls381_g2_default(ForeignInst::Hash2CurveResult));

        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        let total_avail_rounds = Self::max_rounds(k);

        for _ in 0..total_avail_rounds - total_used_instructions {
            for k in 0..2 {
                for i in 0..16 {
                    let (limb, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&default_entries[2 * i + 32 * k], &default_entries[2 * i + 1 + 32 * k]],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(limb);
                }
            }

            for i in 0..16 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![
                        &default_entries[2 * i + 64],
                        &default_entries[2 * i + 1 + 64],
                    ],
                    Fr::from_u128(1u128 << 54),
                    false,
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = default_entries[96].clone();

            let (limb, _) = config.assign_one_line(
                region,
                &mut offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                false,
            )?;
            r.push(limb);
        }

        Ok(r)
    }

    fn synthesize(
        &mut self,
        offset: &mut usize,
        arg_cells: &Vec<Limb<Fr>>,
        region: &mut Region<Fr>,
    ) -> Result<(), Error> {
        *offset = {
            println!("hash2curve adaptor total args is {}", arg_cells.len());
            let mut local_offset = *offset;
            let timer = start_timer!(|| "assign");
            let config = self.config.clone();

            self.initialize(&config, region, &mut local_offset)?;
            for arg_group in arg_cells.chunks_exact(HASH2CURVE_SIZE).into_iter() {
                let args = arg_group.into_iter().map(|x| x.clone());
                let args = args.collect::<Vec<_>>();
                //println!("args {:?}", args);
                self.map2curve(
                    region,
                    &mut local_offset,
                    &args[0..16].to_vec().try_into().unwrap(),
                    &args[16..32].to_vec().try_into().unwrap(),
                )?;
            }
            end_timer!(timer);
            local_offset
        };
        Ok(())
    }

    fn synthesize_separate(
        &mut self,
        _arg_cells: &Vec<Limb<Fr>>,
        _layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        Ok(())
    }
}