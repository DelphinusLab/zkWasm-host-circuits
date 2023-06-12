use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

pub const BN256FQ_SIZE: usize = 5;
pub const BN256G1_SIZE: usize = 11;
pub const BN256G2_SIZE: usize = 21;

use crate::circuits::bn256::{
    Bn256PairChip,
    Bn256SumChip,
    Bn256ChipConfig,
};


use crate::circuits::HostOpSelector;

use crate::host::ForeignInst;

impl HostOpSelector for Bn256PairChip<Fr> {
    type Config = Bn256ChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
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
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::Bn254PairG1 as u64),
            Fr::from(ForeignInst::Bn254PairG2 as u64),
            Fr::from(ForeignInst::Bn254PairG3 as u64),
        ];
        let mut arg_cells = vec![];
        /* The 0,2's u54 of every Fq(5 * u54) return true, others false  */
        let merge_next = |i: usize| {
            let mut r = i % BN256FQ_SIZE;
            if i >= BN256G1_SIZE - 1 {
                r += BN256FQ_SIZE - 1;
            }
            if i >= BN256G1_SIZE + BN256G2_SIZE - 1 {
                r += BN256FQ_SIZE - 1;
            }
            r %= BN256FQ_SIZE;
            r % 2 == 0 && r != BN256FQ_SIZE - 1
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
                    || Ok(shared_operands[offset]),
                )?;

                region.assign_advice(
                    || "picked opcodes",
                    filtered_opcodes,
                    picked_offset,
                    || Ok(opcode.clone()),
                )?;

                region.assign_advice(
                    || "picked index",
                    filtered_index,
                    picked_offset,
                    || Ok(shared_index[offset]),
                )?;

                let value = if toggle >= 0 {
                    shared_operands[offset]
                        .clone()
                        .mul(&Fr::from(1u64 << 54))
                        .add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };
                let opcell = region.assign_advice(
                    || "picked merged operands",
                    merged_operands,
                    picked_offset,
                    || Ok(value),
                )?;

                let value = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::from(1u64 << 54)
                } else {
                    arg_cells.append(&mut vec![opcell]);
                    toggle = -1;
                    Fr::zero()
                };
                region.assign_fixed(|| "indicator", indicator, picked_offset, || Ok(value))?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
    }
    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        let a = arg_cells[0..7].to_vec();
        let b = arg_cells[7..20].to_vec();
        let ab = arg_cells[20..56].to_vec();
        self.load_bn256_pair_circuit(&a, &b, &ab, layouter)?;
        Ok(())
    }
}

impl HostOpSelector for Bn256SumChip<Fr> {
    type Config = Bn256ChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
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
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::Bn254SumG1 as u64),
            Fr::from(ForeignInst::Bn254SumResult as u64),
        ];
        let mut arg_cells = vec![];
        /* The 0,2,5,7's u54 of every G1(11 * u54) return true, others false  */
        let merge_next = |i: usize| {
            let r = i % BN256G1_SIZE;
            let s = r % BN256FQ_SIZE;
            s % 2 == 0 && s != BN256FQ_SIZE - 1 && r != BN256G1_SIZE - 1
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
                    || Ok(shared_operands[offset]),
                )?;

                region.assign_advice(
                    || "picked opcodes",
                    filtered_opcodes,
                    picked_offset,
                    || Ok(opcode.clone()),
                )?;

                region.assign_advice(
                    || "picked index",
                    filtered_index,
                    picked_offset,
                    || Ok(shared_index[offset]),
                )?;

                let value = if toggle >= 0 {
                    shared_operands[offset]
                        .clone()
                        .mul(&Fr::from(1u64 << 54))
                        .add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };
                let opcell = region.assign_advice(
                    || "picked merged operands",
                    merged_operands,
                    picked_offset,
                    || Ok(value),
                )?;

                let value = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::from(1u64 << 54)
                } else {
                    arg_cells.append(&mut vec![opcell]);
                    toggle = -1;
                    Fr::zero()
                };
                region.assign_fixed(|| "indicator", indicator, picked_offset, || Ok(value))?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
    }

    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
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
