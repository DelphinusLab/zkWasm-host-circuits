use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::bls12_381::pairing;
use halo2_proofs::pairing::bls12_381::{G1Affine, G2Affine};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};

pub const BLS381FR_SIZE: usize = 5;
//pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;
pub const BLS381GT_SIZE: usize = 96;
const BLSPAIR_SIZE: usize = BLS381G1_SIZE + BLS381G2_SIZE + BLS381GT_SIZE;
const BLSSUM_SIZE: usize = 1 + BLS381FR_SIZE + 2 * BLS381G1_SIZE;

use crate::circuits::bls::{Bls381ChipConfig, Bls381PairChip, Bls381SumChip};

use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::utils::Limb;

use super::get_selected_entries;
use crate::host::{ExternalHostCallEntry, ForeignInst};

const TOTAL_CONSTRUCTIONS_PAIR: usize = 1;
const TOTAL_CONSTRUCTIONS_SUM: usize = 16;

fn bls381_fr_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for _ in 0..BLS381FR_SIZE {
        r.push(ExternalHostCallEntry {
            op: op as usize,
            value: 0u64,
            is_ret: false,
        });
    }
    r
}

fn bls381_g1_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1Affine::default();
    r.append(&mut crate::adaptor::fr_to_args(a.x, 8, 54, op));
    // G1Affine's default a.x = 0, a.y = 1, can't use a.y, use a.x twice
    r.append(&mut crate::adaptor::fr_to_args(a.x, 8, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: a.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bls381_g1_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1Affine::generator();
    r.append(&mut crate::adaptor::fr_to_args(a.x, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.y, 8, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: a.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bls381_g2_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let b = G2Affine::generator();
    r.append(&mut crate::adaptor::fr_to_args(b.x.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.x.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.y.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.y.c1, 8, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: b.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bls381_gt_pairing_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1Affine::generator();
    let b = G2Affine::generator();
    let ab = pairing(&a, &b);
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c0.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c0.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c1.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c1.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c2.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c2.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c0.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c0.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c1.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c1.c1, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c2.c0, 8, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c2.c1, 8, 54, op));
    r
}

impl HostOpSelector for Bls381PairChip<Fr> {
    type Config = Bls381ChipConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Bls381PairChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bls381PairChip::construct(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS_PAIR)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::BlsPairG1 as u64),
            Fr::from(ForeignInst::BlsPairG2 as u64),
            Fr::from(ForeignInst::BlsPairG3 as u64),
        ]
    }

    fn assign(
        region: &Region<Fr>,
        k: usize,
        _offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();

        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        assert!(selected_entries.len() % BLSPAIR_SIZE == 0);
        let total_used_instructions = selected_entries.len() / BLSPAIR_SIZE;

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BLSPAIR_SIZE) {
            for i in 0..8 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2 * i], &group[2 * i + 1]],
                    Fr::from_u128(1u128 << 54),
                    true,
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = *group.get(16).clone().unwrap();

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

            for i in 0..16 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2 * i + 17], &group[2 * i + 1 + 17]],
                    Fr::from_u128(1u128 << 54),
                    true,
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = *group.get(49).clone().unwrap();

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

            for i in 0..48 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2 * i + 50], &group[2 * i + 1 + 50]],
                    Fr::from_u128(1u128 << 54),
                    true,
                )?;
                r.push(limb);
            }
        }

        let mut default_table = vec![];
        default_table.append(&mut bls381_g1_generator(ForeignInst::BlsPairG1));
        default_table.append(&mut bls381_g2_generator(ForeignInst::BlsPairG2));
        default_table.append(&mut bls381_gt_pairing_generator(ForeignInst::BlsPairG3));

        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        let total_avail_rounds = Self::max_rounds(k);

        for _ in 0..total_avail_rounds - total_used_instructions {
            for i in 0..8 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&default_entries[2 * i], &default_entries[2 * i + 1]],
                    Fr::from_u128(1u128 << 54),
                    false,
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = default_entries[16].clone();

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

            for i in 0..16 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![
                        &default_entries[2 * i + 17],
                        &default_entries[2 * i + 1 + 17],
                    ],
                    Fr::from_u128(1u128 << 54),
                    false,
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = default_entries[49].clone();

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

            for i in 0..48 {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![
                        &default_entries[2 * i + 50],
                        &default_entries[2 * i + 1 + 50],
                    ],
                    Fr::from_u128(1u128 << 54),
                    false,
                )?;
                r.push(limb);
            }
        }
        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let a = arg_cells[0..9].to_vec();
        let b = arg_cells[9..26].to_vec();
        let ab = arg_cells[26..74].to_vec();
        self.load_bls381_pair_circuit(&a, &b, &ab, layouter)?;
        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _local_region: &Region<Fr>,
        _helper: &(),
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl HostOpSelector for Bls381SumChip<Fr> {
    type Config = Bls381ChipConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Bls381SumChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bls381SumChip::construct(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS_SUM)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::BlsSumNew as u64),
            Fr::from(ForeignInst::BlsSumScalar as u64),
            Fr::from(ForeignInst::BlsSumG1 as u64),
            Fr::from(ForeignInst::BlsSumResult as u64),
        ]
    }

    fn assign(
        region: &Region<Fr>,
        k: usize,
        _offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        assert!(selected_entries.len() % BLSSUM_SIZE == 0);
        let total_used_instructions = selected_entries.len() / BLSSUM_SIZE;

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BLSSUM_SIZE) {
            // whether new is zero or not
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            let (limb, _op) = config.assign_one_line(
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

            //Fr  (5 * u54, 3 limbs)
            for i in 0..2 {
                let (p_01, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[1 + 2 * i], &group[2 + 2 * i]],
                    Fr::from_u128(1u128 << 54),
                    true,
                )?;
                r.push(p_01);
            }
            let ((operand, opcode), index) = *group.get(5).clone().unwrap();
            let (limb, _op) = config.assign_one_line(
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

            //G1 and Sum
            for k in 0..2 {
                for i in 0..8 {
                    let (limb, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&group[6 + 2 * i + 17 * k], &group[6 + 2 * i + 17 * k + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(limb);
                }

                let ((operand, opcode), index) = *group.get(22 + 17 * k).clone().unwrap();

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
        }

        let mut default_table = vec![];
        default_table.push(ExternalHostCallEntry {
            op: ForeignInst::BlsSumNew as usize,
            value: 1u64,
            is_ret: false,
        });
        default_table.append(&mut bls381_fr_default(ForeignInst::BlsSumScalar));
        default_table.append(&mut bls381_g1_default(ForeignInst::BlsSumG1));
        default_table.append(&mut bls381_g1_default(ForeignInst::BlsSumResult));

        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        let total_avail_rounds = Self::max_rounds(k);

        for _ in 0..total_avail_rounds - total_used_instructions {
            // whether new is zero or not
            let ((operand, opcode), index) = default_entries[0].clone();
            let (limb, _op) = config.assign_one_line(
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

            //Fr  (5 * u54, 3 limbs)
            for i in 0..2 {
                let (p_01, _op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&default_entries[1 + 2 * i], &default_entries[2 + 2 * i]],
                    Fr::from_u128(1u128 << 54),
                    false,
                )?;
                r.push(p_01);
            }
            let ((operand, opcode), index) = default_entries[5].clone();
            let (limb, _op) = config.assign_one_line(
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

            //G1 and Sum
            for k in 0..2 {
                for i in 0..8 {
                    let (limb, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![
                            &default_entries[6 + 2 * i + 17 * k],
                            &default_entries[6 + 2 * i + 17 * k + 1],
                        ],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(limb);
                }

                let ((operand, opcode), index) = default_entries[22 + 17 * k].clone();

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
        }
        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        self.load_bls381_sum_circuit(&arg_cells, layouter)?;
        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _local_region: &Region<Fr>,
        _helper: &(),
    ) -> Result<(), Error> {
        Ok(())
    }
}
