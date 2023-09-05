//use ark_std::{end_timer, start_timer};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::host::ForeignInst::{MerkleAddress, MerkleGet, MerkleSet, MerkleSetRoot, MerkleGetRoot};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;

use crate::circuits::merkle::MerkleChip;
use crate::circuits::poseidon::PoseidonGateConfig;
use crate::circuits::CommonGateConfig;

use crate::circuits::host::{HostOpConfig, HostOpSelector};

use crate::host::merkle::{MerkleNode, MerkleTree};
use crate::host::mongomerkle::MongoMerkle;
use crate::host::mongomerkle::DEFAULT_HASH_VEC;
use crate::utils::bytes_to_u64;
use crate::utils::data_to_bytes;
use crate::utils::field_to_bytes;
use crate::utils::Limb;

/* The calling convention will be
 * MerkleAddress
 * MerkleSetRoot
 * MerkleSet / MerkleGet
 * MerkleGetRoot
 */
const MERGE_SIZE: usize = 4;
const MERGE_DATA_SIZE: usize = 2;
// 0: set/get 1-4: root 5-8:address 9-12:value 13-16:root
const CHUNK_SIZE: usize = 1 + 3 * MERGE_SIZE; // should equal to 13
const TOTAL_CONSTRUCTIONS: usize = 600;

fn kvpair_new(address: u64) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: MerkleAddress as usize,
        value: address,
        is_ret: false,
    }]
}

fn kvpair_to_host_call_table(
    inputs: &Vec<(u64, Fr, Fr, [Fr; 2], ForeignInst)>,
) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for (addr, root, new_root, value, op) in inputs.into_iter() {
        r.push(kvpair_new(*addr));
        r.push(crate::adaptor::fr_to_args(*root, 4, 64, MerkleSetRoot));
        for v in value.iter() {
            r.push(crate::adaptor::fr_to_args(*v, 2, 64, *op));
        }
        r.push(crate::adaptor::fr_to_args(*new_root, 4, 64, MerkleGetRoot));
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
            Fr::from(MerkleGetRoot as u64),
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

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(MerkleAddress as u64));

            //println!("opcode {:?} {:?}", opcode, operand);

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

            let (limb_new_root, _) = config.assign_merged_operands(
                region,
                &mut offset,
                vec![&group[9], &group[10], &group[11], &group[12]],
                Fr::from_u128(1u128 << 64),
                true,
            )?;
            r.push(limb_new_root);

            for subgroup in group[5..9]
                .into_iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_DATA_SIZE)
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
            0,
            Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[DEPTH])),
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

            // new root does not change
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

            for subgroup in default_entries[5..9]
                .iter()
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
        let default_index = 1u64 << DEPTH;
        layouter.assign_region(
            || "poseidon hash region",
            |mut region| {
                let mut offset = 0;
                let config = self.config.clone();
                self.initialize(&config, &mut region, &mut offset)?;
                // Initialize the mongodb
                // 0: address
                // 1: root
                // 2: new_root
                // 3: value[]
                // 5: op_code
                let mut mt: Option<MongoMerkle<DEPTH>> = None;
                for args in arg_cells.chunks_exact(6) {
                    let [address, root, new_root, value0, value1, opcode] = args else { unreachable!() };
                    //println!("offset {} === op = {:?}", offset, opcode.value);
                    //println!("address is {}", address.value.get_lower_128());
                    //println!("root update is {:?} {:?}", root.value, new_root.value);
                    //println!("value is {:?} {:?}", value0.value, value1.value);
                    let addr = address.value.get_lower_128();
                    let index = (addr as u64) + default_index - 1;
                    let proof = if opcode.value == Fr::from(MerkleSet as u64) {
                        //println!("op is set, process set:");
                        let (mut leaf, _) = mt
                            .as_ref()
                            .unwrap()
                            .get_leaf_with_proof(index)
                            .expect("get leaf error");
                        leaf.set(
                            &data_to_bytes(vec![value0.value, value1.value]).to_vec(),
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
                            field_to_bytes(&root.value),
                            None,
                        ));

                        let (_, proof) = mt
                            .as_ref()
                            .unwrap()
                            .get_leaf_with_proof(index)
                            .expect("get leaf error");

                        proof
                    };
                    /*
                    println!("assist: {:?}", bytes_to_field::<Fr>(&proof.assist[0]));
                    println!("root: {:?}", bytes_to_field::<Fr>(&proof.root));
                    assert!(mt.as_ref().unwrap().verify_proof(&proof).unwrap());
                    */
                    self.assign_proof(
                        &mut region,
                        &mut offset,
                        &proof,
                        &opcode,
                        &address,
                        &root,
                        &new_root,
                        [&value0, &value1],
                    )?;
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
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::host::mongomerkle::MongoMerkle;
    use crate::host::mongomerkle::DEFAULT_HASH_VEC;
    use crate::host::ExternalHostCallEntryTable;
    use crate::host::ForeignInst::{MerkleGet, MerkleSet};
    use crate::utils::bytes_to_field;
    use crate::utils::bytes_to_u64;
    use crate::utils::field_to_bytes;
    use crate::MERKLE_DEPTH;
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

    #[test]
    fn generate_kvpair_input_get_set() {
        let root_default = Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[MERKLE_DEPTH]));
        let address = (1_u64 << MERKLE_DEPTH as u32) - 1;
        let index = 0;
        let data = Fr::from(0x1000 as u64);
        let mut mt = MongoMerkle::<MERKLE_DEPTH>::construct(
            [0u8; 32],
            DEFAULT_HASH_VEC[MERKLE_DEPTH].clone(),
            None,
        );
        let (mut leaf, _) = mt.get_leaf_with_proof(address).unwrap();
        let bytesdata = field_to_bytes(&data).to_vec();
        println!("bytes_data is {:?}", bytesdata);
        leaf.set(&bytesdata);
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root64_new = bytes_to_field(&mt.get_root_hash());

        let default_table = kvpair_to_host_call_table(&vec![
            (index, root_default, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root_default, root64_new, [data, Fr::zero()], MerkleSet),
        ]);
        let file = File::create("kvpair_test1.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }

    #[test]
    fn generate_kvpair_input_gets_set() {
        let root_default = Fr::from_raw(bytes_to_u64(&DEFAULT_HASH_VEC[MERKLE_DEPTH]));
        let index = 1;
        let address = (1_u64 << (MERKLE_DEPTH as u32)) - 1 + index;
        let data = Fr::from(0x1000 as u64);

        let mut mt = MongoMerkle::<MERKLE_DEPTH>::construct(
            [0u8; 32],
            DEFAULT_HASH_VEC[MERKLE_DEPTH].clone(),
            None,
        );
        let (mut leaf, _) = mt.get_leaf_with_proof(address).unwrap();
        let bytesdata = field_to_bytes(&data).to_vec();
        println!("bytes_data is {:?}", bytesdata);
        leaf.set(&bytesdata);
        mt.set_leaf_with_proof(&leaf).unwrap();
        let root64_new = bytes_to_field(&mt.get_root_hash());

        let default_table = kvpair_to_host_call_table(&vec![
            (index + 1, root_default, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root_default, root_default, [Fr::zero(), Fr::zero()], MerkleGet),
            (index, root_default, root64_new, [data, Fr::zero()], MerkleSet),
        ]);
        let file = File::create("kvpair_test2.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }
}
