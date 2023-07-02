use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{ConstraintSystem, Error},
};
use halo2_proofs::arithmetic::FieldExt;

pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;
pub const BLS381GT_SIZE: usize = 96;
const BLSARGS_SIZE: usize = BLS381G1_SIZE + BLS381G2_SIZE + BLS381GT_SIZE;


use std::ops::Mul;
use crate::circuits::bls::{
    Bls381PairChip,
    Bls381SumChip,
    Bls381ChipConfig,
};

use crate::circuits::{HostOpSelector, HostOpConfig, Limb};

use crate::host::ForeignInst;

impl HostOpSelector for Bls381PairChip<Fr> {
    type Config = Bls381ChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
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


        let entries = shared_operands.clone().into_iter().zip(shared_opcodes.clone()).zip(shared_index.clone());

        let selected_entries = entries.filter(|((_operand, opcode), _index)| {
            opcodes.contains(opcode)
        }).collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(selected_entries.len() % BLSARGS_SIZE == 0);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(BLSARGS_SIZE) {
            for i in 0..8 {
                let limb = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2*i], &group[2*i+1]],
                    Fr::from_u128(1u128 << 54)
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = *group.get(16).clone().unwrap();

            let cell = config.assign_one_line(region, &mut offset, operand, opcode, index,
               operand, Fr::zero())?;
            r.push(Limb::new(Some(cell), operand));

            for i in 0..16 {
                let limb = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2*i+17], &group[2*i+1+17]],
                    Fr::from_u128(1u128 << 54)
                )?;
                r.push(limb);
            }

            let ((operand, opcode), index) = *group.get(49).clone().unwrap();

            let cell = config.assign_one_line(region, &mut offset, operand, opcode, index,
               operand, Fr::zero())?;
            r.push(Limb::new(Some(cell), operand));

            for i in 0..48 {
                let limb = config.assign_merged_operands(
                    region,
                    &mut offset,
                    vec![&group[2*i+50], &group[2*i+1+50]],
                    Fr::from_u128(1u128 << 54)
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
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
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
                config.assign_cell(region, picked_offset, &HostOpConfig::filtered_operand(), shared_operands[offset])?;
                config.assign_cell(region, picked_offset, &HostOpConfig::filtered_opcode(), opcode.clone())?;
                config.assign_cell(region, picked_offset, &HostOpConfig::filtered_index(), shared_index[offset])?;

                let value = if toggle >= 0 {
                    shared_operands[offset]
                        .clone()
                        .mul(&Fr::from(1u64 << 54))
                        .add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };

                let opcell = config.assign_cell(region, picked_offset, &HostOpConfig::merged_op(), value)?;

                let ind = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::from(1u64 << 54)
                } else {
                    arg_cells.append(&mut vec![Limb::new(Some(opcell), value)]);
                    toggle = -1;
                    Fr::zero()
                };
                config.assign_cell(region, picked_offset, &HostOpConfig::indicator(), ind)?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
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

