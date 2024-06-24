use crate::adaptor::get_selected_entries;
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::circuits::keccak256::KeccakChip;
use crate::circuits::keccak256::KeccakGateConfig;
use crate::host::keccak256::KECCAK_HASHER;
use crate::host::ForeignInst::{Keccak256Finalize, Keccak256New, Keccak256Push};
use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
use crate::utils::Limb;
use ark_std::{end_timer, start_timer};
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::{Advice, Column, ConstraintSystem, Error};

fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: Keccak256New as usize,
        value: if restart { 1u64 } else { 0u64 },
        is_ret: false,
    }]
}

// 1 + 17 + 4
fn hash_to_host_call_table(inputs: &[Fr; 17], result: &[Fr; 4]) -> ExternalHostCallEntryTable {
    let mut r = vec![];
    r.push(hash_cont(true));
    for f in inputs.iter() {
        r.push(crate::adaptor::fr_to_args(*f, 1, 64, Keccak256Push));
    }
    for f in result.iter() {
        r.push(crate::adaptor::fr_to_args(*f, 1, 64, Keccak256Finalize));
    }
    ExternalHostCallEntryTable(r.into_iter().flatten().collect())
}

const TOTAL_CONSTRUCTIONS: usize = 50;

impl HostOpSelector for KeccakChip<Fr> {
    type Config = KeccakGateConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config {
        KeccakChip::<Fr>::configure(meta, shared_advice)
    }

    fn construct(c: Self::Config) -> Self {
        KeccakChip::<Fr>::construct(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::Keccak256New as u64),
            Fr::from(ForeignInst::Keccak256Push as u64),
            Fr::from(ForeignInst::Keccak256Finalize as u64),
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
        let opcodes: Vec<Fr> = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);

        let total_used_instructions = selected_entries.len() / (1 + 17 + 4);
        println!(" selected entries: {:?}", total_used_instructions);

        let mut r = vec![];

        // TODO: Change 8 to RATE ?
        for group in selected_entries.chunks_exact(1 + 17 + 4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert_eq!(opcode.clone(), Fr::from(Keccak256New as u64));
            let (limb, _op) = config.assign_one_line(
                //operand, opcode
                region,
                offset,
                operand,
                opcode,
                index,
                operand,    //same as operand as indicator is 0
                Fr::zero(), //not merged
                true,       // in filtered table
            )?;
            r.push(limb);

            for subgroup in group.into_iter().skip(1) {
                let ((operand, opcode), index) = subgroup.clone();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,    //same as operand as indicator is 0
                    Fr::zero(), //not merged
                    true,       // in filtered table
                )?;
                r.push(limb);
            }
        }

        let default_table = hash_to_host_call_table(
            &[
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
            &KECCAK_HASHER.clone().squeeze().map(|x| Fr::from(x)),
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

            for subgroup in default_entries.clone().into_iter().skip(1) {
                let ((operand, opcode), index) = subgroup.clone();
                let (limb, _op) = config.assign_one_line(
                    region,
                    offset,
                    operand,
                    opcode,
                    index,
                    operand,    //same as operand as indicator is 0
                    Fr::zero(), //not merged
                    false,      // in filtered table
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
        _helper: &(),
    ) -> Result<(), Error> {
        println!("keccak total args is {}", arg_cells.len());
        *offset = {
            println!("keccak adaptor total args is {}", arg_cells.len());
            let mut local_offset = *offset;
            let timer = start_timer!(|| "assign");
            let config = self.config.clone();
            self.initialize(&config, region, &mut local_offset)?;
            for arg_group in arg_cells.chunks_exact(22).into_iter() {
                let args = arg_group.into_iter().map(|x| x.clone());
                let args = args.collect::<Vec<_>>();
                //println!("args {:?}", args);
                self.assign_permute(
                    region,
                    &mut local_offset,
                    &args[1..18].to_vec().try_into().unwrap(),
                    &args[0],
                    &args[18..22].to_vec().try_into().unwrap(),
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
    use crate::host::ForeignInst::{Keccak256Finalize, Keccak256New, Keccak256Push};
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable};
    use crate::utils::field_to_u64;
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

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
            let result = hasher.update_exact(&round.map(|x| field_to_u64(&x)));
            for f in result.iter() {
                r.push(crate::adaptor::fr_to_args(
                    Fr::from(*f),
                    1,
                    64,
                    Keccak256Finalize,
                ));
            }
        }
        ExternalHostCallEntryTable(r.into_iter().flatten().collect())
    }

    #[test]
    fn generate_keccak_input_single() {
        let table = hash_to_host_call_table(vec![[
            Fr::one(),
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
                Fr::from(1u64 << 63),
            ],
        ]);
        let file = File::create("keccak256_test_multi.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_keccak_input_multi_byte() {
        let table = hash_to_host_call_table(vec![
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [Fr::one(); 17],
            [
                Fr::one(),
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
                Fr::from(1u64 << 63),
            ],
        ]);
        let file = File::create("keccak256_test_multi_byte.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
