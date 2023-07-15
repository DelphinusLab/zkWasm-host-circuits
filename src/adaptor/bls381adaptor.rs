use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{ConstraintSystem, Error},
};

//pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;
pub const BLS381GT_SIZE: usize = 96;
const BLSPAIR_SIZE: usize = BLS381G1_SIZE + BLS381G2_SIZE + BLS381GT_SIZE;
const BLSSUM_SIZE: usize = BLS381G1_SIZE * 3;

use crate::circuits::bls::{Bls381ChipConfig, Bls381PairChip, Bls381SumChip};

use crate::circuits::host::{HostOpConfig, HostOpSelector};

use crate::host::ForeignInst;
use crate::utils::Limb;

impl HostOpSelector for Bls381PairChip<Fr> {
    type Config = Bls381ChipConfig;
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        Bls381PairChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bls381PairChip::construct(c)
    }
    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::BlspairG1 as u64),
            Fr::from(ForeignInst::BlspairG2 as u64),
            Fr::from(ForeignInst::BlspairG3 as u64),
        ];

        let entries = shared_operands
            .clone()
            .into_iter()
            .zip(shared_opcodes.clone())
            .zip(shared_index.clone());

        let selected_entries = entries
            .filter(|((_operand, opcode), _index)| opcodes.contains(opcode))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(selected_entries.len() % BLSPAIR_SIZE == 0);

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
        Ok(r)
    }
    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let a = arg_cells[0..9].to_vec();
        let b = arg_cells[9..26].to_vec();
        let ab = arg_cells[26..74].to_vec();
        self.load_bls381_pair_circuit(&a, &b, &ab, layouter)?;
        Ok(())
    }
}

impl HostOpSelector for Bls381SumChip<Fr> {
    type Config = Bls381ChipConfig;
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        Bls381SumChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Bls381SumChip::construct(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::BlsSumG1 as u64),
            Fr::from(ForeignInst::BlsSumResult as u64),
        ];

        let entries = shared_operands
            .clone()
            .into_iter()
            .zip(shared_opcodes.clone())
            .zip(shared_index.clone());

        let selected_entries = entries
            .filter(|((_operand, opcode), _index)| opcodes.contains(opcode))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(selected_entries.len() % BLSSUM_SIZE == 0);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BLS381G1_SIZE) {
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
        Ok(r)
    }

    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let len = arg_cells.len();
        let args = arg_cells[0..len - 9].to_vec();
        let ret = arg_cells[len - 9..len].to_vec();
        self.load_bls381_sum_circuit(&args, &ret, layouter)?;
        Ok(())
    }
}
