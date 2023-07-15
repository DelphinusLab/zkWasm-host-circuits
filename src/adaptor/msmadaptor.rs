use crate::host::ExternalHostCallEntry;
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;

use crate::circuits::babyjub::{AltJubChip, Point as CircuitPoint};
use crate::circuits::CommonGateConfig;
use crate::host::ForeignInst::{JubjubSumNew, JubjubSumPush, JubjubSumResult};

use crate::circuits::host::{HostOpConfig, HostOpSelector};

use crate::adaptor::field_to_bn;
use crate::host::jubjub::Point;
use crate::utils::Limb;

const MERGE_SIZE: usize = 4;
const CHUNK_SIZE: usize = 1 + (2 + 1 + 2) * MERGE_SIZE;

const TOTAL_CONSTRUCTIONS: usize = 2;

fn msm_new(restart: bool) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: JubjubSumNew as usize,
        value: if restart { 1u64 } else { 0u64 },
        is_ret: false,
    }]
}

fn msm_to_host_call_table<F: FieldExt>(inputs: &Vec<(Point, F)>) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    let mut start = true;
    let mut result = Point::identity();
    for (p, c) in inputs.into_iter() {
        r.push(msm_new(start));
        r.push(crate::adaptor::fr_to_args(p.x, 4, 64, JubjubSumPush));
        r.push(crate::adaptor::fr_to_args(p.y, 4, 64, JubjubSumPush));
        r.push(crate::adaptor::fr_to_args(*c, 4, 64, JubjubSumPush));
        result = result.add(&p.mul_scalar(&field_to_bn(c)));
        r.push(crate::adaptor::fr_to_args(result.x, 4, 64, JubjubSumResult));
        r.push(crate::adaptor::fr_to_args(result.y, 4, 64, JubjubSumResult));
        start = false;
    }
    r.into_iter().flatten().collect::<Vec<_>>()
}

impl HostOpSelector for AltJubChip<Fr> {
    type Config = CommonGateConfig;
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        AltJubChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        AltJubChip::new(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(JubjubSumNew as u64),
            Fr::from(JubjubSumPush as u64),
            Fr::from(JubjubSumResult as u64),
        ];

        let entries = shared_operands
            .clone()
            .into_iter()
            .zip(shared_opcodes.clone())
            .zip(shared_index.clone());

        let selected_entries = entries
            .filter(|((_operand, opcode), _index)| opcodes.contains(opcode))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        let total_used_instructions = selected_entries.len() / (CHUNK_SIZE);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(JubjubSumNew as u64));

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

            for subgroup in group
                .clone()
                .into_iter()
                .skip(1)
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                let (limb, _) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    true,
                )?;
                r.push(limb);
            }
        }

        let default_table = msm_to_host_call_table(&vec![(Point::identity(), Fr::one())]);

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        for _ in 0..TOTAL_CONSTRUCTIONS - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(JubjubSumNew as u64));

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

            for subgroup in default_entries
                .clone()
                .iter()
                .skip(1)
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                let (limb, _) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    false,
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
        println!("total args is {}", arg_cells.len());
        layouter.assign_region(
            || "poseidon hash region",
            |mut region| {
                let mut offset = 0;
                let timer = start_timer!(|| "assign");
                let config = self.config.clone();
                self.initialize(&config, &mut region, &mut offset)?;
                // arg_cells format 1 + 2 + 1 + 2
                for arg_group in arg_cells.chunks_exact(6).into_iter() {
                    let args = arg_group.into_iter().map(|x| x.clone());
                    let args = args.collect::<Vec<_>>();
                    self.assign_incremental_msm(
                        &mut region,
                        &mut offset,
                        &CircuitPoint {
                            x: args[1].clone(),
                            y: args[2].clone(),
                        },
                        &args[3],
                        &args[0],
                        &CircuitPoint {
                            x: args[4].clone(),
                            y: args[5].clone(),
                        },
                    )?;
                }
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::msm_to_host_call_table;
    use crate::host::jubjub::Point;
    use crate::host::ExternalHostCallEntryTable;
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

    #[test]
    fn generate_jubjub_msm_input() {
        let default_table = msm_to_host_call_table(&vec![(Point::identity(), Fr::one())]);
        let file = File::create("jubjub.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }

    #[test]
    fn generate_jubjub_msm_input_multi() {
        let default_table = msm_to_host_call_table(&vec![(Point::identity(), Fr::one())]);
        let file = File::create("jubjub_multi.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }
}
