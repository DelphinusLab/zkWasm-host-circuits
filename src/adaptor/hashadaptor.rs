use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{VirtualCells, Error, Expression};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Region, Layouter};
use crate::host::{
    ForeignInst,
    ExternalHostCallEntryTable,
    ExternalHostCallEntry,
};
use crate::host::ForeignInst::{
    PoseidonNew,
    PoseidonPush,
    PoseidonFinalize,
};
use crate::circuits::LookupAssistConfig;
use crate::circuits::poseidon::PoseidonChip;
use crate::circuits::CommonGateConfig;
use crate::circuits::LookupAssistChip;
use crate::host::poseidon::gen_hasher;

use crate::circuits::host::{
    HostOpSelector,
    HostOpConfig,
};

use crate::utils::Limb;

impl LookupAssistConfig for () {
    /// register a column (col) to be range checked by limb size (sz)
    fn register<F: FieldExt> (
        &self,
        _cs: &mut ConstraintSystem<F>,
        _col: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        _hint: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) {
        ()
    }
}

impl<F:FieldExt> LookupAssistChip<F> for () {
    fn provide_lookup_evidence (
        &mut self,
        _region: &mut Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }
}

fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
    vec![ExternalHostCallEntry {
        op: PoseidonNew as usize,
        value: if restart {1u64} else {0u64},
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

const TOTAL_CONSTRUCTIONS:usize = 2048;

impl HostOpSelector for PoseidonChip<Fr> {
    type Config = CommonGateConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config {
        PoseidonChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        PoseidonChip::construct(c)
    }


    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::PoseidonNew as u64),
            Fr::from(ForeignInst::PoseidonPush as u64),
            Fr::from(ForeignInst::PoseidonFinalize as u64),
        ];

        let entries = shared_operands.clone().into_iter().zip(shared_opcodes.clone()).zip(shared_index.clone());

        let selected_entries = entries.filter(|((_operand, opcode), _index)| {
            opcodes.contains(opcode)
        }).collect::<Vec<((Fr, Fr), Fr)>>();

        let total_used_instructions = selected_entries.len()/(1+8*4+4);

        let mut offset = 0;
        let mut r = vec![];

        // TODO: Change 8 to RATE ?
        for group in selected_entries.chunks_exact(1+8*4+4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

            let (limb, _op) = config.assign_one_line(
                region, &mut offset, operand, opcode, index,
                operand,
                Fr::zero(),
                true
            )?;
            r.push(limb);

            for subgroup in group.clone().into_iter().skip(1).collect::<Vec<_>>().chunks_exact(4) {
                let (limb, _op) = config.assign_merged_operands(region, &mut offset, subgroup.to_vec(), Fr::from_u128(1u128 << 64), true)?;
                r.push(limb);
            }
        }

        let default_table = hash_to_host_call_table([
                Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()
            ], gen_hasher().squeeze());

        //let entries = default_table.
        let default_entries:Vec<((Fr, Fr), Fr)> = default_table.0.into_iter().map(
            |x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero())
        ).collect::<Vec<((Fr, Fr), Fr)>>();

        for _ in 0..TOTAL_CONSTRUCTIONS - total_used_instructions {
            let ((operand, opcode), index) = default_entries[0].clone();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

            let (limb, _op) = config.assign_one_line(
                region, &mut offset, operand, opcode, index,
                operand,
                Fr::zero(),
                false
            )?;
            r.push(limb);

            for subgroup in default_entries.clone().iter().skip(1).collect::<Vec<_>>().chunks_exact(4) {
                let (limb, _op) = config.assign_merged_operands(region, &mut offset, subgroup.to_vec(), Fr::from_u128(1u128 << 64), false)?;
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
                for arg_group in arg_cells.chunks_exact(10).into_iter() {
                    let args = arg_group.into_iter().map(|x| x.clone());
                    let args = args.collect::<Vec<_>>();
                    self.assign_permute(
                        &mut region,
                        &mut offset,
                        &args[1..9].to_vec().try_into().unwrap(),
                        &args[0],
                        &args[9],
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
    use halo2_proofs::pairing::bn256::Fr;
    use crate::host::{
        ExternalHostCallEntryTable,
        ExternalHostCallEntry,
    };
    use std::fs::File;

    use crate::host::ForeignInst::{
        PoseidonNew,
        PoseidonPush,
        PoseidonFinalize,
    };

    fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
        vec![ExternalHostCallEntry {
            op: PoseidonNew as usize,
            value: if restart {1u64} else {0u64},
            is_ret: false,
        }]

    }

    fn hash_to_host_call_table(inputs: Vec<[Fr; 8]>) -> ExternalHostCallEntryTable {
        let mut r = vec![];
        let mut start = true;
        let mut hasher = crate::host::poseidon::gen_hasher();
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
        let table = hash_to_host_call_table(
            vec![[Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()]],
        );
        let file = File::create("poseidontest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_poseidon_input_multi() {
        let table = hash_to_host_call_table(
            vec![
                [Fr::one(); 8],
                [Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()],
            ],
        );
        let file = File::create("poseidontest_multi.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

}
