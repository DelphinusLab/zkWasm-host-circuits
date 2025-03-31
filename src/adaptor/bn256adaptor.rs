use super::get_selected_entries;
use halo2_proofs::pairing::bn256::pairing;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::pairing::bn256::{G1Affine, G2Affine, G1, G2};
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};

pub const BN256FR_SIZE: usize = 4;
//pub const BN256FQ_SIZE: usize = 5;
pub const BN256G1_SIZE: usize = 11;
pub const BN256G2_SIZE: usize = 21;
pub const BN256GT_SIZE: usize = 60;

const BN256PAIR_SIZE: usize = BN256G1_SIZE + BN256G2_SIZE + BN256GT_SIZE;
const BN256SUM_SIZE: usize = 1 + BN256FR_SIZE + 2 * BN256G1_SIZE;

use crate::circuits::bn256::{Bn256ChipConfig, Bn256PairChip, Bn256SumChip};

use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::utils::Limb;

use crate::host::{ExternalHostCallEntry, ForeignInst};

const TOTAL_CONSTRUCTIONS_PAIR: usize = 1;
const TOTAL_CONSTRUCTIONS_SUM: usize = 32;

fn bn256_fr_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for _ in 0..BN256FR_SIZE {
        r.push(ExternalHostCallEntry {
            op: op as usize,
            value: 0u64,
            is_ret: false,
        });
    }
    r
}

fn bn256_g1_default(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1::default();
    r.append(&mut crate::adaptor::fr_to_args(a.x, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.y, 5, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: a.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bn256_g1_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1::generator();
    r.append(&mut crate::adaptor::fr_to_args(a.x, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(a.y, 5, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: a.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bn256_g2_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let b = G2::generator();
    r.append(&mut crate::adaptor::fr_to_args(b.x.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.x.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.y.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(b.y.c1, 5, 54, op));
    r.push(ExternalHostCallEntry {
        op: op as usize,
        value: b.is_identity().unwrap_u8() as u64,
        is_ret: false,
    });
    r
}

fn bn256_gt_pairing_generator(op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let a = G1::generator();
    let b = G2::generator();
    let a_af = G1Affine::from(a);
    let b_af = G2Affine::from(b);
    let ab = pairing(&a_af, &b_af);
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c0.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c0.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c1.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c1.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c2.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c0.c2.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c0.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c0.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c1.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c1.c1, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c2.c0, 5, 54, op));
    r.append(&mut crate::adaptor::fr_to_args(ab.0.c1.c2.c1, 5, 54, op));
    r
}

impl HostOpSelector for Bn256PairChip<Fr> {
    type Config = Bn256ChipConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Bn256PairChip::<Fr>::configure(meta)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS_PAIR)
    }

    fn construct(c: Self::Config) -> Self {
        Bn256PairChip::construct(c)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::Bn254PairG1 as u64),
            Fr::from(ForeignInst::Bn254PairG2 as u64),
            Fr::from(ForeignInst::Bn254PairG3 as u64),
        ]
    }

    fn assign(
        region: &Region<Fr>,
        k: usize,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        assert!(selected_entries.len() % BN256PAIR_SIZE == 0);
        let total_used_instructions = selected_entries.len() / BN256PAIR_SIZE;

        assert_eq!(*offset, 0);

        let mut r = vec![];

        for group in selected_entries.chunks_exact(BN256PAIR_SIZE) {
            // get g1_x and g1_y: ((1,1) (1,1) 1) * 2
            for j in 0..2 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![&group[5 * j + 2 * i], &group[5 * j + 2 * i + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4).clone().unwrap();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    true,
                )?;
                r.push(p_2);
            }

            // whether g1 is zero or not
            let ((operand, opcode), index) = *group.get(10).clone().unwrap();

            let (g1zero, _op) = config.assign_one_line(
                region,
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                true,
            )?;
            r.push(g1zero);

            for j in 0..4 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![&group[5 * j + 2 * i + 11], &group[5 * j + 2 * i + 1 + 11]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4 + 11).clone().unwrap();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    true,
                )?;
                r.push(p_2);
            }

            // whether g2 is zero or not
            let ((operand, opcode), index) = *group.get(31).clone().unwrap();

            let (g2zero, _op) = config.assign_one_line(
                region,
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                true,
            )?;
            r.push(g2zero);

            for j in 0..12 {
                for i in 0..2 {
                    let (q, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![&group[5 * j + 2 * i + 32], &group[5 * j + 2 * i + 1 + 32]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(q);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4 + 32).clone().unwrap();
                let (q, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    true,
                )?;
                r.push(q);
            }
        }

        let mut default_table = vec![];
        default_table.append(&mut bn256_g1_generator(ForeignInst::Bn254PairG1));
        default_table.append(&mut bn256_g2_generator(ForeignInst::Bn254PairG2));
        default_table.append(&mut bn256_gt_pairing_generator(ForeignInst::Bn254PairG3));

        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        let total_avail_rounds = Self::max_rounds(k);

        for _ in 0..total_avail_rounds - total_used_instructions {
            // get g1_x and g1_y: ((1,1) (1,1) 1) * 2
            for j in 0..2 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![
                            &default_entries[5 * j + 2 * i],
                            &default_entries[5 * j + 2 * i + 1],
                        ],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = default_entries[5 * j + 4].clone();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    false,
                )?;
                r.push(p_2);
            }

            // whether g1 is zero or not
            let ((operand, opcode), index) = default_entries[10].clone();

            let (g1zero, _op) = config.assign_one_line(
                region,
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                false,
            )?;
            r.push(g1zero);

            for j in 0..4 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![
                            &default_entries[5 * j + 2 * i + 11],
                            &default_entries[5 * j + 2 * i + 1 + 11],
                        ],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = default_entries[5 * j + 4 + 11].clone();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    false,
                )?;
                r.push(p_2);
            }

            // whether g2 is zero or not
            let ((operand, opcode), index) = default_entries[31].clone();

            let (g2zero, _op) = config.assign_one_line(
                region,
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                false,
            )?;
            r.push(g2zero);

            for j in 0..12 {
                for i in 0..2 {
                    let (q, _op) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![
                            &default_entries[5 * j + 2 * i + 32],
                            &default_entries[5 * j + 2 * i + 1 + 32],
                        ],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(q);
                }
                let ((operand, opcode), index) = default_entries[5 * j + 4 + 32].clone();
                let (q, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,
                    Fr::zero(),
                    false,
                )?;
                r.push(q);
            }
        }
        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let a = arg_cells[0..7].to_vec();
        let b = arg_cells[7..20].to_vec();
        let ab = arg_cells[20..56].to_vec();
        self.load_bn256_pair_circuit(&a, &b, &ab, layouter)?;
        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _region: &Region<Fr>,
        _helper: &(),
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl HostOpSelector for Bn256SumChip<Fr> {
    type Config = Bn256ChipConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Bn256SumChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bn256SumChip::construct(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS_SUM)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::Bn254SumNew as u64),
            Fr::from(ForeignInst::Bn254SumScalar as u64),
            Fr::from(ForeignInst::Bn254SumG1 as u64),
            Fr::from(ForeignInst::Bn254SumResult as u64),
        ]
    }

    fn assign(
        region: &Region<Fr>,
        k: usize,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);
        assert!(selected_entries.len() % BN256SUM_SIZE == 0);
        let total_used_instructions = selected_entries.len() / BN256SUM_SIZE;

        assert_eq!(*offset, 0);
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BN256SUM_SIZE) {
            // whether new is zero or not
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            let (limb, _op) = config.assign_one_line(
                region,
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                true,
            )?;
            r.push(limb);

            // Fr
            let (limb, _op) = config.assign_merged_operands(
                region,
                offset,
                vec![&group[1], &group[2], &group[3], &group[4]],
                Fr::from_u128(1u128 << 64),
                true,
            )?;
            r.push(limb);

            // G1 and sum
            for k in 0..2 {
                for j in 0..2 {
                    for i in 0..2 {
                        let (p_01, _op) = config.assign_merged_operands(
                            region,
                            offset,
                            vec![
                                &group[5 + 5 * j + 2 * i + 11 * k],
                                &group[5 + 5 * j + 2 * i + 11 * k + 1],
                            ],
                            Fr::from_u128(1u128 << 54),
                            true,
                        )?;
                        r.push(p_01);
                    }
                    let ((operand, opcode), index) =
                        *group.get(5 + 5 * j + 11 * k + 4).clone().unwrap();
                    let (p_2, _op) = config.assign_one_line(
                        region,
                        offset,
                        operand,
                        opcode,
                        index,
                        operand,
                        Fr::zero(),
                        true,
                    )?;
                    r.push(p_2);
                }

                // whether z is zero or not
                let ((operand, opcode), index) = *group.get(15 + 11 * k).clone().unwrap();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
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
            op: ForeignInst::Bn254SumNew as usize,
            value: 1u64,
            is_ret: false,
        });
        default_table.append(&mut bn256_fr_default(ForeignInst::Bn254SumScalar));
        default_table.append(&mut bn256_g1_default(ForeignInst::Bn254SumG1));
        default_table.append(&mut bn256_g1_default(ForeignInst::Bn254SumResult));

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
                offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                false,
            )?;
            r.push(limb);

            // Fr
            let (limb, _op) = config.assign_merged_operands(
                region,
                offset,
                vec![
                    &default_entries[1],
                    &default_entries[2],
                    &default_entries[3],
                    &default_entries[4],
                ],
                Fr::from_u128(1u128 << 64),
                false,
            )?;
            r.push(limb);

            // G1 and sum
            for k in 0..2 {
                for j in 0..2 {
                    for i in 0..2 {
                        let (p_01, _op) = config.assign_merged_operands(
                            region,
                            offset,
                            vec![
                                &default_entries[5 + 5 * j + 2 * i + 11 * k],
                                &default_entries[5 + 5 * j + 2 * i + 11 * k + 1],
                            ],
                            Fr::from_u128(1u128 << 54),
                            false,
                        )?;
                        r.push(p_01);
                    }
                    let ((operand, opcode), index) =
                        default_entries[5 + 5 * j + 11 * k + 4].clone();
                    let (p_2, _op) = config.assign_one_line(
                        region,
                        offset,
                        operand,
                        opcode,
                        index,
                        operand,
                        Fr::zero(),
                        false,
                    )?;
                    r.push(p_2);
                }

                // whether z is zero or not
                let ((operand, opcode), index) = default_entries[15 + 11 * k].clone();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
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
        self.load_bn256_sum_circuit(&arg_cells, layouter)?;
        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _region: &Region<Fr>,
        _helper: &(),
    ) -> Result<(), Error> {
        Ok(())
    }
}
