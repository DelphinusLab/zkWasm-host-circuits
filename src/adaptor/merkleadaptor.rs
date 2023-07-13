//use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Error;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Region, Layouter};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::host::ForeignInst::{
    KVPairAddress,
    KVPairSetRoot,
    KVPairSet,
    KVPairGet,
};

use crate::circuits::merkle::MerkleChip;
use crate::circuits::CommonGateConfig;

use crate::circuits::host::{
    HostOpSelector,
    HostOpConfig,
};

use crate::utils::Limb;
use crate::host::merkle::{
    MerkleTree,
    MerkleNode,
};
use crate::host::kvpair::MongoMerkle;
use crate::utils::field_to_bytes;
use crate::utils::data_to_bytes;

// Some constants for the purpose of deault entries
const DEFAULT_ROOT_HASH64: [u64; 4] = [
    14768724118053802825,
    12044759864135545626,
    7296277131441537979,
    802061392934800187,
];

lazy_static::lazy_static! {
    static ref DEFAULT_ROOT_HASH: Fr = Fr::from_raw(DEFAULT_ROOT_HASH64);
}


/* The calling convention will be
 * KVPairAddress
 * KVPairSetRoot
 * KVPairSet / KVPairGet
 */
const MERGE_SIZE:usize = 4;
const MERGE_DATA_SIZE:usize = 2;
// 0: set/get 1-4: root 5-8:address 9-12:value
const CHUNK_SIZE:usize = 1 + 1*MERGE_SIZE + 1*MERGE_SIZE; // should equal to 9
const TOTAL_CONSTRUCTIONS:usize = 2;

fn kvpair_new(address: u64) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: KVPairAddress as usize,
        value: address,
        is_ret: false,
    }]
}

fn kvpair_to_host_call_table<F:FieldExt>(inputs: &Vec<(u64, F, F, ForeignInst)>) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    for (addr, root, value, op) in inputs.into_iter() {
        r.push(kvpair_new(*addr));
        r.push(crate::adaptor::fr_to_args(*root, 4, 64, ForeignInst::KVPairSetRoot));
        r.push(crate::adaptor::fr_to_args(*value, 4, 64, *op));
    }
    r.into_iter().flatten().collect::<Vec<_>>()
}



impl HostOpSelector for MerkleChip<Fr, 20> {
    type Config = CommonGateConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
        MerkleChip::<Fr, 20>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        MerkleChip::new(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(KVPairSetRoot as u64),
            Fr::from(KVPairAddress as u64),
            Fr::from(KVPairSet as u64),
            Fr::from(KVPairGet as u64),
        ];

        let entries = shared_operands.clone().into_iter().zip(shared_opcodes.clone()).zip(shared_index.clone());

        let selected_entries = entries.filter(|((_operand, opcode), _index)| {
            opcodes.contains(opcode)
        }).collect::<Vec<((Fr, Fr), Fr)>>();

        let total_used_instructions = selected_entries.len()/(CHUNK_SIZE);

        let mut offset = 0;
        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(KVPairAddress as u64));

            let (limb, op) = config.assign_one_line(
                region, &mut offset, operand, opcode, index,
                operand,
                Fr::zero(),
                true
            )?;
            println!("detect address is {:?}", limb.value);
            r.push(limb);

            let mut setget = op;

            let (limb, _) = config.assign_merged_operands(region, &mut offset, vec![&group[1], &group[2], &group[3], &group[4]], Fr::from_u128(1u128 << 64), true)?;
            r.push(limb);

            for subgroup in group.clone().into_iter().skip(5).collect::<Vec<_>>().chunks_exact(2) {
                let (limb, op) = config.assign_merged_operands(region, &mut offset, subgroup.to_vec(), Fr::from_u128(1u128 << 64), true)?;
                setget = op;
                r.push(limb);
            }
            r.push(setget);
        }

        let default_table = kvpair_to_host_call_table(&vec![(0u64, *DEFAULT_ROOT_HASH, Fr::zero(), KVPairGet)]);

        //let entries = default_table.
        let default_entries:Vec<((Fr, Fr), Fr)> = default_table.into_iter().map(
            |x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero())
        ).collect::<Vec<((Fr, Fr), Fr)>>();

        for _ in 0..TOTAL_CONSTRUCTIONS - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(KVPairAddress as u64));

            let (limb, op) = config.assign_one_line(
                region, &mut offset, operand, opcode, index,
                operand,
                Fr::zero(),
                false
            )?;
            r.push(limb);

            let mut setget = op;

            let (limb, _) = config.assign_merged_operands(region, &mut offset,
                vec![&default_entries[1], &default_entries[2], &default_entries[3], &default_entries[4]], Fr::from_u128(1u128 << 64), true)?;
            r.push(limb);

            for subgroup in default_entries.clone().iter().skip(5).collect::<Vec<_>>().chunks_exact(MERGE_DATA_SIZE) {
                let (limb, op) = config.assign_merged_operands(region, &mut offset, subgroup.to_vec(), Fr::from_u128(1u128 << 64), false)?;
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
        println!("total args is {}", arg_cells.len());
        layouter.assign_region(
            || "poseidon hash region",
            |mut region| {
                let mut offset = 0;
                const DEFAULT_ROOT_HASH_BYTES: [u8; 32] = [
                    73, 83, 87, 90, 86, 12, 245, 204, 26, 115, 174, 210, 71, 149, 39, 167, 187, 3, 97, 202,
                    100, 149, 65, 101, 59, 11, 239, 93, 150, 126, 33, 11,
                ];

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
                let mut mt:Option<MongoMerkle> = None;
                for arg_group in arg_cells.chunks_exact(5) {
                    println!("round ====== ");
                    println!("address is {}", arg_group[0].value.get_lower_128());
                    println!("set root with is {:?} [op = {:?}]", arg_group[1].value, arg_group[4].value);
                    println!("value is {:?} {:?}", arg_group[2].value, arg_group[3].value);
                    let proof = if arg_group[4].value == Fr::from(KVPairSet as u64) {
                        println!("op is set, process set:");
                        let (mut leaf, _) = mt.as_ref().unwrap().get_leaf_with_proof(arg_group[0].value.get_lower_128() as u32)
                            .expect("get leaf error");
                        leaf.set(&data_to_bytes(vec![arg_group[2].value, arg_group[3].value]).to_vec());
                        mt.as_mut().unwrap().set_leaf_with_proof(&leaf).expect("set leaf error")
                    } else {
                        // the case of get value:
                        // 1. load db
                        // 2. get leaf
                        println!("op is get, process get");
                        mt = Some(MongoMerkle::construct([0u8;32], field_to_bytes(&arg_group[1].value)));

                        let (_, proof) = mt.as_ref().unwrap().get_leaf_with_proof(arg_group[0].value.get_lower_128() as u32)
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
    use halo2_proofs::pairing::bn256::Fr;
    use crate::host::ExternalHostCallEntryTable;
    use super::kvpair_to_host_call_table;
    use std::fs::File;
    use crate::host::ForeignInst::{
        KVPairSet,
        KVPairGet,
    };
    use crate::host::kvpair::MongoMerkle;
    use crate::host::merkle::MerkleTree;
    use super::DEFAULT_ROOT_HASH;

    #[test]
    fn generate_kvpair_input() {
        const TEST_ADDR: [u8; 32] = [2; 32];
        const NEW_ROOT_HASH64: [u64; 4] = [
            16039362344330646748,
            7125397509397931624,
            4246510858682859310,
            1093404808759360274,
        ];
        const DEFAULT_ROOT_HASH_BYTES: [u8; 32] = [
            73, 83, 87, 90, 86, 12, 245, 204, 26, 115, 174, 210, 71, 149, 39, 167, 187, 3, 97, 202,
            100, 149, 65, 101, 59, 11, 239, 93, 150, 126, 33, 11,
        ];

        let mut _mt = MongoMerkle::construct(TEST_ADDR, DEFAULT_ROOT_HASH_BYTES);
        let root_default = DEFAULT_ROOT_HASH.clone();
        let index = 2_u64.pow(20) - 1;
        let data = 0x1000;
        let root64_new = Fr::from_raw(NEW_ROOT_HASH64);

        let default_table = kvpair_to_host_call_table(&vec![
            (index, root_default, Fr::zero(), KVPairGet),
            (index, root64_new, Fr::from(data), KVPairSet)
        ]);
        let file = File::create("kvpair.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table)).expect("can not write to file");
    }
}
