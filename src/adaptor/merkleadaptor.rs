use std::cell::RefCell;
use std::rc::Rc;
//use ark_std::{end_timer, start_timer};
use crate::adaptor::get_selected_entries;
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::circuits::merkle::MerkleChip;
use crate::circuits::poseidon::PoseidonGateConfig;
use crate::circuits::CommonGateConfig;
use crate::host::db::TreeDB;
use crate::host::merkle::{MerkleNode, MerkleTree};
use crate::host::mongomerkle::{MongoMerkle, DEFAULT_HASH_VEC};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::host::ForeignInst::{MerkleAddress, MerkleGet, MerkleGetRoot, MerkleSet, MerkleSetRoot};
use crate::utils::data_to_bytes;
use crate::utils::field_to_bytes;
use crate::utils::Limb;
use ff::PrimeField;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;

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

const TOTAL_CONSTRUCTIONS: usize = 1080;

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
    type Helper = Option<Rc<RefCell<dyn TreeDB>>>; // known tree db if provided
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        MerkleChip::<Fr, DEPTH>::configure(meta, shared_advices)
    }

    fn construct(c: Self::Config) -> Self {
        MerkleChip::new(c.0, c.1)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(MerkleSetRoot as u64),
            Fr::from(MerkleGetRoot as u64),
            Fr::from(MerkleAddress as u64),
            Fr::from(MerkleSet as u64),
            Fr::from(MerkleGet as u64),
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

        let total_used_instructions = selected_entries.len() / (CHUNK_SIZE);

        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(MerkleAddress as u64));

            //println!("opcode {:?} {:?}", opcode, operand);

            let (limb, op) = config.assign_one_line(
                region,
                offset,
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

            // address
            let (limb, _) = config.assign_merged_operands(
                region,
                offset,
                vec![&group[1], &group[2], &group[3], &group[4]],
                Fr::from_u128(1u128 << 64),
                true,
            )?;
            r.push(limb);

            // setget
            for subgroup in group[5..9]
                .into_iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_DATA_SIZE)
            {
                let (limb, op) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    true,
                )?;
                setget = op;
                r.push(limb);
            }

            // new root
            let (limb_new_root, _) = config.assign_merged_operands(
                region,
                offset,
                vec![&group[9], &group[10], &group[11], &group[12]],
                Fr::from_u128(1u128 << 64),
                true,
            )?;
            r.push(limb_new_root);

            r.push(setget);
        }

        let mt: MongoMerkle<DEPTH> = MongoMerkle::<DEPTH>::default();
        let default_proof = mt.default_proof();
        assert!(mt.verify_proof(&default_proof).unwrap() == true);

        let default_table = kvpair_to_host_call_table(&vec![(
            0,
            Fr::from_repr(default_proof.root).unwrap(),
            Fr::from_repr(default_proof.root).unwrap(),
            [Fr::zero(), Fr::zero()],
            MerkleGet,
        )]);

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(k >= 22);
        let total_available = Self::max_rounds(k);
        assert!(total_used_instructions <= total_available);
        println!("total available instructions {}", total_available);

        for _ in 0..=total_available - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(MerkleAddress as u64));

            let (limb, op) = config.assign_one_line(
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

            let mut setget = op;

            let (limb, _) = config.assign_merged_operands(
                region,
                offset,
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

            // set or get
            for subgroup in default_entries[5..9]
                .iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_DATA_SIZE)
            {
                let (limb, op) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    false,
                )?;
                setget = op;
                r.push(limb);
            }

            // new root does not change
            let (limb, _) = config.assign_merged_operands(
                region,
                offset,
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

            r.push(setget);
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
        helper: &Self::Helper,
    ) -> Result<(), Error> {
        let default_index = 1u64 << DEPTH;
        *offset = {
            let config = self.config.clone();
            let mut local_offset = *offset;
            self.initialize(&config, region, &mut local_offset)?;
            // Initialize the mongodb
            // 0: address
            // 1: root
            // 2: new_root
            // 3: value[]
            // 5: op_code
            let mut mt: MongoMerkle<DEPTH> = if let Some(tree_db) = helper {
                MongoMerkle::construct([0u8; 32], DEFAULT_HASH_VEC[DEPTH], Some(tree_db.clone()))
            } else {
                MongoMerkle::<DEPTH>::default()
            };
            let default_proof = mt.default_proof();

            for args in arg_cells.chunks_exact(6) {
                let [address, root, value0, value1, new_root, opcode] = args else { unreachable!() };
                //println!("local_offset {} === op = {:?}", local_offset, opcode.value);
                //println!("address is {}", address.value.get_lower_128());
                //println!("root update is {:?} {:?}", root.value, new_root.value);
                //println!("value is {:?} {:?}", value0.value, value1.value);
                let addr = address.value.get_lower_128();
                let index = (addr as u64) + default_index - 1;
                let is_set = opcode.value == Fr::from(MerkleSet as u64);
                let proof = if index == default_proof.index
                    && field_to_bytes(&new_root.value) == default_proof.root
                {
                    default_proof.clone()
                } else {
                    if is_set {
                        //println!("op is set, process set:");
                        let (mut leaf, _) = mt.get_leaf_with_proof(index).expect("get leaf error");
                        leaf.set(&data_to_bytes(vec![value0.value, value1.value]).to_vec());
                        mt.set_leaf_with_proof(&leaf).expect("set leaf error")
                    } else {
                        // the case of get value:
                        // 1. load db
                        // 2. get leaf
                        //println!("op is get, process get");
                        mt.update_root_hash(&field_to_bytes(&root.value));
                        let (_, proof) = mt.get_leaf_with_proof(index).expect("get leaf error");

                        proof
                    }
                };
                /*
                println!("assist: {:?}", bytes_to_field::<Fr>(&proof.assist[0]));
                println!("root: {:?}", bytes_to_field::<Fr>(&proof.root));
                assert!(mt.as_ref().unwrap().verify_proof(&proof).unwrap());
                */

                self.assign_proof(
                    region,
                    &mut local_offset,
                    &proof,
                    &opcode,
                    &address,
                    &root,
                    &new_root,
                    [&value0, &value1],
                )?;
            }
            local_offset
        };
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
    use crate::proof::MERKLE_DEPTH;
    use crate::utils::bytes_to_field;
    use crate::utils::bytes_to_u64;
    use crate::utils::field_to_bytes;
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
            (
                index,
                root_default,
                root_default,
                [Fr::zero(), Fr::zero()],
                MerkleGet,
            ),
            (
                index,
                root_default,
                root64_new,
                [data, Fr::zero()],
                MerkleSet,
            ),
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
            (
                index + 1,
                root_default,
                root_default,
                [Fr::zero(), Fr::zero()],
                MerkleGet,
            ),
            (
                index,
                root_default,
                root_default,
                [Fr::zero(), Fr::zero()],
                MerkleGet,
            ),
            (
                index,
                root_default,
                root64_new,
                [data, Fr::zero()],
                MerkleSet,
            ),
        ]);
        let file = File::create("kvpair_test2.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }
}
