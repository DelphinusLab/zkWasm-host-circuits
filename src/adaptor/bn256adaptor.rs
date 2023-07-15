use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::{ConstraintSystem, Error},
};

//pub const BN256FQ_SIZE: usize = 5;
pub const BN256G1_SIZE: usize = 11;
pub const BN256G2_SIZE: usize = 21;
pub const BN256GT_SIZE: usize = 60;

const BN256PAIR_SIZE: usize = BN256G1_SIZE + BN256G2_SIZE + BN256GT_SIZE;
const BN256SUM_SIZE: usize = BN256G1_SIZE * 3;

use crate::circuits::bn256::{Bn256ChipConfig, Bn256PairChip, Bn256SumChip};

use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::utils::Limb;

use crate::host::ForeignInst;

impl HostOpSelector for Bn256PairChip<Fr> {
    type Config = Bn256ChipConfig;
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        Bn256PairChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bn256PairChip::construct(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::Bn254PairG1 as u64),
            Fr::from(ForeignInst::Bn254PairG2 as u64),
            Fr::from(ForeignInst::Bn254PairG3 as u64),
        ];

        let entries = shared_operands
            .clone()
            .into_iter()
            .zip(shared_opcodes.clone())
            .zip(shared_index.clone());

        let selected_entries = entries
            .filter(|((_operand, opcode), _index)| opcodes.contains(opcode))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(selected_entries.len() % BN256PAIR_SIZE == 0);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BN256PAIR_SIZE) {
            // get g1_x and g1_y: ((1,1) (1,1) 1) * 2
            for j in 0..2 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&group[5 * j + 2 * i], &group[5 * j + 2 * i + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4).clone().unwrap();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    &mut offset,
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
                &mut offset,
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
                        &mut offset,
                        vec![&group[5 * j + 2 * i + 11], &group[5 * j + 2 * i + 1 + 11]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4 + 11).clone().unwrap();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    &mut offset,
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
                &mut offset,
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
                        &mut offset,
                        vec![&group[5 * j + 2 * i + 32], &group[5 * j + 2 * i + 1 + 32]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(q);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4 + 32).clone().unwrap();
                let (q, _op) = config.assign_one_line(
                    region,
                    &mut offset,
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
        Ok(r)
    }

    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let a = arg_cells[0..7].to_vec();
        let b = arg_cells[7..20].to_vec();
        let ab = arg_cells[20..56].to_vec();
        println!("ab is: {:?}", ab);
        self.load_bn256_pair_circuit(&a, &b, &ab, layouter)?;
        Ok(())
    }
}

impl HostOpSelector for Bn256SumChip<Fr> {
    type Config = Bn256ChipConfig;
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        Bn256SumChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bn256SumChip::construct(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::Bn254SumG1 as u64),
            Fr::from(ForeignInst::Bn254SumResult as u64),
        ];

        let entries = shared_operands
            .clone()
            .into_iter()
            .zip(shared_opcodes.clone())
            .zip(shared_index.clone());

        let selected_entries = entries
            .filter(|((_operand, opcode), _index)| opcodes.contains(opcode))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(selected_entries.len() % BN256SUM_SIZE == 0);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BN256G1_SIZE) {
            for j in 0..2 {
                for i in 0..2 {
                    let (p_01, _op) = config.assign_merged_operands(
                        region,
                        &mut offset,
                        vec![&group[5 * j + 2 * i], &group[5 * j + 2 * i + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(p_01);
                }
                let ((operand, opcode), index) = *group.get(5 * j + 4).clone().unwrap();
                let (p_2, _op) = config.assign_one_line(
                    region,
                    &mut offset,
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
        }
        println!("r: {:?} with length {}", r, r.len());
        Ok(r)
    }

    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let len = arg_cells.len();
        let args = arg_cells[0..len - 7].to_vec();
        let ret = arg_cells[len - 7..len].to_vec();
        self.load_bn256_sum_circuit(&args, &ret, layouter)?;
        Ok(())
    }
}
