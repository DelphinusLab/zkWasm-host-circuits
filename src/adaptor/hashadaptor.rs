use crate::adaptor::get_selected_entries;
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::circuits::poseidon::PoseidonChip;
use crate::circuits::poseidon::PoseidonGateConfig;
use crate::circuits::CommonGateConfig;
use crate::circuits::LookupAssistChip;
use crate::circuits::LookupAssistConfig;
use crate::host::poseidon::POSEIDON_HASHER;
use crate::host::poseidon::POSEIDON_HASHER_SPEC;
use crate::host::ForeignInst::{PoseidonFinalize, PoseidonNew, PoseidonPush};
use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::{Advice, Column, Error, Expression, VirtualCells};

use crate::utils::Limb;
use rayon::prelude::*;
impl LookupAssistConfig for () {
    /// register a column (col) to be range checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        _cs: &mut ConstraintSystem<F>,
        _col: impl FnOnce(&mut VirtualCells<F>) -> Vec<Expression<F>>,
    ) {
        ()
    }
}

impl<F: FieldExt> LookupAssistChip<F> for () {
    fn provide_lookup_evidence(
        &mut self,
        _region: &Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }
}

fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: PoseidonNew as usize,
        value: if restart { 1u64 } else { 0u64 },
        is_ret: false,
    }]
}

fn hash_to_host_call_table(inputs: [Fr; 8], result: Fr) -> ExternalHostCallEntryTable {
    let mut r = vec![];
    r.push(hash_cont(true));
    for f in inputs.iter() {
        r.push(crate::adaptor::fr_to_args(*f, 4, 64, PoseidonPush));
    }
    r.push(crate::adaptor::fr_to_args(result, 4, 64, PoseidonFinalize));
    ExternalHostCallEntryTable(r.into_iter().flatten().collect())
}

const TOTAL_CONSTRUCTIONS: usize = 2048;

impl HostOpSelector for PoseidonChip<Fr, 9, 8> {
    type Config = (CommonGateConfig, PoseidonGateConfig);
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        PoseidonChip::<Fr, 9, 8>::configure(meta, shared_advices)
    }

    fn construct(c: Self::Config) -> Self {
        PoseidonChip::construct(c.0, c.1, POSEIDON_HASHER_SPEC.clone())
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::PoseidonNew as u64),
            Fr::from(ForeignInst::PoseidonPush as u64),
            Fr::from(ForeignInst::PoseidonFinalize as u64),
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
        let total_used_instructions = selected_entries.len() / (1 + 8 * 4 + 4);

        let mut r = vec![];

        // TODO: Change 8 to RATE ?
        for group in selected_entries.chunks_exact(1 + 8 * 4 + 4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

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

            for subgroup in group
                .clone()
                .into_iter()
                .skip(1)
                .collect::<Vec<_>>()
                .chunks_exact(4)
            {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    true,
                )?;
                r.push(limb);
            }
        }

        let default_table = hash_to_host_call_table(
            [
                Fr::one(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
            ],
            POSEIDON_HASHER.clone().squeeze(),
        );

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .0
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(k >= 22);
        let total_available = Self::max_rounds(k);
        assert!(total_used_instructions <= total_available);

        for _ in 0..=total_available - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

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

            for subgroup in default_entries
                .clone()
                .iter()
                .skip(1)
                .collect::<Vec<_>>()
                .chunks_exact(4)
            {
                let (limb, _op) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    false,
                )?;
                r.push(limb);
            }
        }

        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        _arg_cells: &Vec<Limb<Fr>>,
        _layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn synthesize(
        &mut self,
        offset: &mut usize,
        arg_cells: &Vec<Limb<Fr>>,
        region: &Region<Fr>,
    ) -> Result<(), Error> {
        let mhy_synthesize_timer = start_timer!(|| "mhy_synthesize_timer");
        println!("total args is {}", arg_cells.len());
        let threads: usize = 10;
        //10 arg_cells into a group, divide by threads number
        let chunk_size = (arg_cells.len() / 10 + threads - 1) / threads;
        *offset = {
            let mut local_offset = *offset;
            let timer = start_timer!(|| "assign");
            let config = self.config.clone();
            self.initialize(&config, region, &mut local_offset)?;
            let mut poseidon_chips: Vec<_> = vec![];
            let mut offset_vec: Vec<usize> = vec![];
            //arrange offsets, poseidon_chips( and poseidon states) for each thread
            poseidon_chips.push(self.clone());
            offset_vec.push(local_offset);
            for index in 1..threads {
                poseidon_chips.push(self.clone());
                offset_vec.push(local_offset + index * 1260 * chunk_size);
                let args = arg_cells[1 + chunk_size * index * threads
                    ..1 + self.poseidon_state.state.len() + chunk_size * index * threads]
                    .into_iter()
                    .map(|x| x.clone())
                    .collect::<Vec<_>>();
                poseidon_chips[index].poseidon_state.state = args.try_into().unwrap();
            }
            //chunk_size * 10 is total arg cells assigned to a thread
            let arg_groups = arg_cells.chunks_exact(10 * chunk_size).collect::<Vec<_>>();
            //zip args, offsets, and poseidon_chips then start par_iter
            let mut combined_vec: Vec<_> = arg_groups
                .into_iter()
                .zip(offset_vec.into_iter())
                .zip(poseidon_chips.into_iter())
                .map(|((x, y), z)| (x, y, z))
                .collect();
            combined_vec
                .par_iter_mut()
                .for_each(|(arg_group, mut offset_parallel, chip)| {
                    println!("int par_iter with offsel  {:?}", offset_parallel);
                    let par_timer = start_timer!(|| "par_iter with offset");
                    for arg_chunks in arg_group.chunks_exact(10).into_iter() {
                        let args = arg_chunks.into_iter().map(|x| x.clone());
                        let args = args.collect::<Vec<_>>();

                        let mut new_state = vec![];
                        for (value, default) in chip
                            .poseidon_state
                            .state
                            .iter()
                            .zip(chip.poseidon_state.default.iter())
                        {
                            new_state.push(chip.config.select(
                                region,
                                &mut (),
                                &mut offset_parallel,
                                &args[0],
                                value,
                                default,
                                chip.round,
                            ));
                        }
                        let new_state_vec: Vec<Limb<Fr>> = new_state
                            .iter()
                            .map(|res| res.as_ref().expect("Error processing Limb"))
                            .cloned()
                            .collect();
                        let new_state_array: [Limb<Fr>; 9] = new_state_vec
                            .try_into()
                            .expect("Expected a Vec of length 9");
                        chip.poseidon_state.state = new_state_array;
                        let args_array: [Limb<Fr>; 8] = args[1..9]
                            .to_vec()
                            .try_into()
                            .expect("Slice must be exactly 8 elements long");
                        chip.poseidon_state.permute(
                            &chip.config,
                            &chip.extend,
                            &chip.spec,
                            region,
                            &mut offset_parallel,
                            &args_array,
                        );
                        let result = chip.poseidon_state.state[1].clone();

                        region.constrain_equal(
                            args[9].cell.as_ref().unwrap().cell(),
                            result.cell.as_ref().unwrap().cell(),
                        );
                    }
                    end_timer!(par_timer);
                });

            end_timer!(timer);
            local_offset + 1260 * arg_cells.len() / 10
        };
        end_timer!(mhy_synthesize_timer);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable};
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

    use crate::host::ForeignInst::{PoseidonFinalize, PoseidonNew, PoseidonPush};

    fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
        vec![ExternalHostCallEntry {
            op: PoseidonNew as usize,
            value: if restart { 1u64 } else { 0u64 },
            is_ret: false,
        }]
    }

    fn hash_to_host_call_table(inputs: Vec<[Fr; 8]>) -> ExternalHostCallEntryTable {
        let mut r = vec![];
        let mut start = true;
        let mut hasher = crate::host::poseidon::POSEIDON_HASHER.clone();
        for round in inputs.into_iter() {
            r.push(hash_cont(start));
            start = false;
            for f in round.iter() {
                r.push(crate::adaptor::fr_to_args(*f, 4, 64, PoseidonPush));
            }
            let result = hasher.update_exact(&round);
            r.push(crate::adaptor::fr_to_args(result, 4, 64, PoseidonFinalize));
        }
        ExternalHostCallEntryTable(r.into_iter().flatten().collect())
    }

    #[test]
    fn generate_poseidon_input() {
        let table = hash_to_host_call_table(vec![[
            Fr::one(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
        ]]);
        let file = File::create("poseidontest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_poseidon_input_multi() {
        let table = hash_to_host_call_table(vec![
            [Fr::one(); 8],
            [
                Fr::one(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
            ],
        ]);
        let file = File::create("poseidontest_multi.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
