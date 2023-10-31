use crate::circuits::keccak256::KeccakChip;
use crate::circuits::CommonGateConfig;
//use crate::circuits::LookupAssistChip;
//use crate::circuits::LookupAssistConfig;
use crate::adaptor::get_selected_entries;
use crate::host::ForeignInst::{Keccak256New, Keccak256Push, Keccak256Finalize};
use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::{ConstraintSystem, Error, Column, Advice}; 
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::host::keccak256::KECCAK_HASHER;
use crate::utils::Limb;

fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: Keccak256New as usize,
        value: if restart { 1u64 } else { 0u64 },
        is_ret: false,
    }]
}

// 1 + 17 + 4
fn hash_to_host_call_table(inputs: [Fr; 17], result: Fr) -> ExternalHostCallEntryTable {
    let mut r = vec![];
    r.push(hash_cont(true));
    for f in inputs.iter() {
        r.push(crate::adaptor::fr_to_args(*f, 1, 64, Keccak256Push));
    }
    r.push(crate::adaptor::fr_to_args(result, 4, 64, Keccak256Finalize));
    ExternalHostCallEntryTable(r.into_iter().flatten().collect())
}

const TOTAL_CONSTRUCTIONS: usize = 12;

impl HostOpSelector for KeccakChip<Fr> {
    type Config = CommonGateConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config {
        KeccakChip::<Fr>::configure(meta, shared_advice)
    }

    fn construct(c: Self::Config) -> Self {
        KeccakChip::<Fr>::construct(c)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::Keccak256New as u64),
            Fr::from(ForeignInst::Keccak256Push as u64),
            Fr::from(ForeignInst::Keccak256Finalize as u64),
        ]
    }

    fn assign(
        region: &mut Region<Fr>,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        let total_used_instructions = selected_entries.len() / (1 + 17 * 4 + 4);

        let mut r = vec![];

        // TODO: Change 8 to RATE ?
        for group in selected_entries.chunks_exact(1 + 17 * 4 + 4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert_eq!(opcode.clone(), Fr::from(Keccak256New as u64));
            let (limb, _op) = config.assign_one_line( //operand, opcode
                region,
                offset,
                operand,
                opcode,
                index,
                operand, //same as operand as indicator is 0
                Fr::zero(), //not merged
                true, // in filtered table
            )?;
            r.push(limb);

            for subgroup in group
                .clone()
                .into_iter()
                .skip(1)
                .take(17)
                .collect::<Vec<_>>()
            {
                let ((operand, opcode), index) = subgroup.clone();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand, //same as operand as indicator is 0
                    Fr::zero(), //not merged
                    true, // in filtered table
                )?;
                r.push(limb);
            }

            for subgroup in group
                .clone()
                .iter()
                .skip(18) //reset
                .collect::<Vec<_>>()
                .chunks_exact(4) // 1 lane
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
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::from(1u64 << 63)
            ],
            KECCAK_HASHER.clone().squeeze(),
        );

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .0
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        //dbg!(total_used_instructions.clone());
        for _ in 0..TOTAL_CONSTRUCTIONS - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert_eq!(opcode.clone(), Fr::from(Keccak256New as u64));

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
                .into_iter()
                .skip(1)
                .take(17)
                .collect::<Vec<_>>()
            {
                let ((operand, opcode), index) = subgroup.clone();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand, //same as operand as indicator is 0
                    Fr::zero(), //not merged
                    true, // in filtered table
                )?;
                r.push(limb);
            }

            for subgroup in default_entries
                .clone()
                .iter()
                .skip(18) //reset
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
        _layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        Ok(())
    }


    fn synthesize(
        &mut self,
        offset: &mut usize,
        arg_cells: &Vec<Limb<Fr>>,
        region: &mut Region<Fr>,
    ) -> Result<(), Error> {
        println!("keccak total args is {}", arg_cells.len());
        *offset = {
            println!("keccak adaptor total args is {}", arg_cells.len());
                let mut local_offset = *offset;
                let timer = start_timer!(|| "assign");
                let config = self.config.clone();
                self.initialize(&config, region, &mut local_offset)?;
                for arg_group in arg_cells.chunks_exact(19).into_iter() {
                    let args = arg_group.into_iter().map(|x| x.clone());
                    let args = args.collect::<Vec<_>>();
                    println!("args {:?}", args);
                    self.assign_permute(
                        region,
                        &mut local_offset,
                        &args[1..18].to_vec().try_into().unwrap(),
                        &args[0],
                        &args[18],
                    )?;
                }
                end_timer!(timer);
                local_offset
        };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable};
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

    use crate::host::ForeignInst::{Keccak256New, Keccak256Finalize, Keccak256Push};

    fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
        vec![ExternalHostCallEntry {
            op: Keccak256New as usize,
            value: if restart { 1u64 } else { 0u64 },
            is_ret: false,
        }]
    }

    fn hash_to_host_call_table(inputs: Vec<[Fr; 17]>) -> ExternalHostCallEntryTable {
        let mut r = vec![];
        let mut start = true;
        let mut hasher = crate::host::keccak256::KECCAK_HASHER.clone();
        for round in inputs.into_iter() {
            r.push(hash_cont(start));
            start = false;
            for f in round.iter() {
                r.push(crate::adaptor::fr_to_args(*f, 1, 64, Keccak256Push));
            }
            let result = hasher.update_exact(&round);
            r.push(crate::adaptor::fr_to_args(result, 4, 64, Keccak256Finalize));
        }
        ExternalHostCallEntryTable(r.into_iter().flatten().collect())
    }

    #[test]
    fn generate_keccak_input() {
        let table = hash_to_host_call_table(vec![[
            Fr::one(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::zero(),
            Fr::from(1u64 << 63),
        ]]);
        let file = File::create("keccak256_test.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_keccak_input_multi() {
        let table = hash_to_host_call_table(vec![
            [Fr::one(); 17],
            [
                Fr::one(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::zero(),
                Fr::from(1u64 << 63),
            ],
        ]);
        let file = File::create("keccak256_test_multi.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
