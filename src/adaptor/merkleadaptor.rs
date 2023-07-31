//use ark_std::{end_timer, start_timer};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::host::ForeignInst::{MerkleAddress, MerkleGet, MerkleSet, MerkleSetRoot};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;

use crate::circuits::merkle::MerkleChip;
use crate::circuits::CommonGateConfig;
use crate::circuits::poseidon::PoseidonGateConfig;

use crate::circuits::host::{HostOpConfig, HostOpSelector};

use crate::host::mongomerkle::MongoMerkle;
use crate::host::mongomerkle::DEFAULT_HASH_VEC;
use crate::host::merkle::{MerkleNode, MerkleTree};
use crate::utils::bytes_to_u64;
use crate::utils::data_to_bytes;
use crate::utils::field_to_bytes;
use crate::utils::Limb;

/* The calling convention will be
 * MerkleAddress
 * MerkleSetRoot
 * MerkleSet / MerkleGet
 */
const MERGE_SIZE: usize = 4;
const MERGE_DATA_SIZE: usize = 2;
// 0: set/get 1-4: root 5-8:address 9-12:value
const CHUNK_SIZE: usize = 1 + 1 * MERGE_SIZE + 1 * MERGE_SIZE; // should equal to 9
const TOTAL_CONSTRUCTIONS: usize = 800;

fn kvpair_new(address: u64) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: MerkleAddress as usize,
        value: address,
        is_ret: false,
    }]
}

fn kvpair_to_host_call_table(
    inputs: &Vec<(u64, Fr, [Fr; 2], ForeignInst)>,
) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for (addr, root, value, op) in inputs.into_iter() {
        r.push(kvpair_new(*addr));
        r.push(crate::adaptor::fr_to_args(
            *root,
            4,
            64,
            MerkleSetRoot,
        ));
        for v in value.iter() {
            r.push(crate::adaptor::fr_to_args(*v, 2, 64, *op));
        }
    }
    r.into_iter().flatten().collect::<Vec<_>>()
}

impl<const DEPTH: usize> HostOpSelector for MerkleChip<Fr, DEPTH> {
    type Config = (CommonGateConfig, PoseidonGateConfig);
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        MerkleChip::<Fr, DEPTH>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        MerkleChip::new(c.0, c.1)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(MerkleSetRoot as u64),
            Fr::from(MerkleAddress as u64),
            Fr::from(MerkleSet as u64),
            Fr::from(MerkleGet as u64),
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
        let default_index = 1u64 << DEPTH;

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(MerkleAddress as u64));

            let (limb, op) = config.assign_one_line(
                region,
                &mut offset,
                operand,
                opcode,
                index,
                operand,
                Fr::zero(),
                true,
            )?;
            //println!("detect address is {:?}", limb.value);
            r.push(limb);

            let mut setget = op;

            let (limb, _) = config.assign_merged_operands(
                region,
                &mut offset,
                vec![&group[1], &group[2], &group[3], &group[4]],
                Fr::from_u128(1u128 << 64),
                true,
            )?;
            r.push(limb);

            for subgroup in group
                .clone()
                .into_iter()
                .skip(5)
                .collect::<Vec<_>>()
                .chunks_exact(2)
            {
                let (limb, op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    true,
                )?;
                setget = op;
                r.push(limb);
            }
            r.push(setget);
        }

        let default_table = kvpair_to_host_call_table(&vec![(
            default_index,
            Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[DEPTH])),
            [Fr::zero(), Fr::zero()],
            MerkleGet,
        )]);

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        for _ in 0..TOTAL_CONSTRUCTIONS - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(MerkleAddress as u64));

            let (limb, op) = config.assign_one_line(
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

            let mut setget = op;

            let (limb, _) = config.assign_merged_operands(
                region,
                &mut offset,
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

            for subgroup in default_entries
                .clone()
                .iter()
                .skip(5)
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_DATA_SIZE)
            {
                let (limb, op) = config.assign_merged_operands(
                    region,
                    &mut offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    false,
                )?;
                setget = op;
                r.push(limb);
            }
            r.push(setget);
        }

        Ok(r)
    }

    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        //println!("total args is {}", arg_cells.len());
        layouter.assign_region(
            || "poseidon hash region",
            |mut region| {
                let mut offset = 0;
                let mut round = 0;

                let config = self.config.clone();
                self.initialize(&config, &mut region, &mut offset)?;
                //
                //
                // Initialize the mongodb
                //
                // 0: address
                // 1: root
                // 2: value[]
                // 4: op_code
                let mut mt: Option<MongoMerkle<DEPTH>> = None;
                for arg_group in arg_cells.chunks_exact(5) {
                    println!("round ====== {} {}", round, offset);
                    round += 1;
                    //println!("address is {}", arg_group[0].value.get_lower_128());
                    //println!("set root with is {:?} [op = {:?}]", arg_group[1].value, arg_group[4].value);
                    //println!("value is {:?} {:?}", arg_group[2].value, arg_group[3].value);
                    let proof = if arg_group[4].value == Fr::from(MerkleSet as u64) {
                        //println!("op is set, process set:");
                        let (mut leaf, _) = mt
                            .as_ref()
                            .unwrap()
                            .get_leaf_with_proof(arg_group[0].value.get_lower_128() as u64)
                            .expect("get leaf error");
                        leaf.set(
                            &data_to_bytes(vec![arg_group[2].value, arg_group[3].value]).to_vec(),
                        );
                        mt.as_mut()
                            .unwrap()
                            .set_leaf_with_proof(&leaf)
                            .expect("set leaf error")
                    } else {
                        // the case of get value:
                        // 1. load db
                        // 2. get leaf
                        //println!("op is get, process get");
                        mt = Some(MongoMerkle::construct(
                            [0u8; 32],
                            field_to_bytes(&arg_group[1].value),
                        ));

                        let (_, proof) = mt
                            .as_ref()
                            .unwrap()
                            .get_leaf_with_proof(arg_group[0].value.get_lower_128() as u64)
                            .expect("get leaf error");
                        proof
                    };
                    println!("assign proof ...");
                    self.assign_proof(
                        &mut region,
                        &mut offset,
                        &proof,
                        &arg_group[4],
                        &arg_group[0],
                        &arg_group[1],
                        [&arg_group[2], &arg_group[3]],
                    )?;
                    println!("finish assign proof ...");
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::kvpair_to_host_call_table;
    use crate::host::mongomerkle::MongoMerkle;
    use crate::host::mongomerkle::DEFAULT_HASH_VEC;
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::host::ExternalHostCallEntryTable;
    use crate::host::ForeignInst::{MerkleGet, MerkleSet};
    use crate::utils::bytes_to_field;
    use crate::utils::bytes_to_u64;
    use crate::utils::field_to_bytes;
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;
    use crate::MERKLE_DEPTH;

    #[test]
    fn generate_kvpair_input_get_set() {
        let root_default = Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[MERKLE_DEPTH]));
        let index = 2_u64.pow(MERKLE_DEPTH as u32) - 1;
        let data = Fr::from(0x1000 as u64);
        let mut mt = MongoMerkle::<MERKLE_DEPTH>::construct([0u8; 32], DEFAULT_HASH_VEC[MERKLE_DEPTH].clone());
        let (mut leaf, _) = mt.get_leaf_with_proof(index).unwrap();
        let bytesdata = field_to_bytes(&data).to_vec();
        println!("bytes_data is {:?}", bytesdata);
        leaf.set(&bytesdata);
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root64_new = bytes_to_field(&mt.get_root_hash());

        let default_table = kvpair_to_host_call_table(&vec![
            (index, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root64_new, [data, Fr::zero()], MerkleSet),
        ]);
        let file = File::create("kvpair_test1.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }

    #[test]
    fn generate_kvpair_input_gets_set() {
        let root_default = Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[MERKLE_DEPTH]));
        let index = 2_u64.pow(MERKLE_DEPTH as u32) - 1;
        let data = Fr::from(0x1000 as u64);

        let mut mt = MongoMerkle::<MERKLE_DEPTH>::construct([0u8; 32], DEFAULT_HASH_VEC[MERKLE_DEPTH].clone());
        let (mut leaf, _) = mt.get_leaf_with_proof(index).unwrap();
        let bytesdata = field_to_bytes(&data).to_vec();
        println!("bytes_data is {:?}", bytesdata);
        leaf.set(&bytesdata);
        mt.set_leaf_with_proof(&leaf).unwrap();
        let root64_new = bytes_to_field(&mt.get_root_hash());

        let default_table = kvpair_to_host_call_table(&vec![
            (index + 1, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root64_new, [data, Fr::zero()], MerkleSet),
        ]);
        let file = File::create("kvpair_test2.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }
}
