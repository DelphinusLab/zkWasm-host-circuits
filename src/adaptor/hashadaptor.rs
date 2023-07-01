use std::fmt::Debug;
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{VirtualCells, Error, Expression};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Region, AssignedCell, Layouter};
use crate::host::ForeignInst;
use crate::host::ForeignInst::PoseidonNew;
use crate::host::{Reduce, ReduceRule};
use crate::circuits::{Limb, LookupAssistConfig};
use crate::circuits::poseidon::PoseidonChip;
use crate::circuits::CommonGateConfig;
use crate::circuits::LookupAssistChip;

use crate::circuits::{
    HostOpSelector,
    HostOpConfig,
};

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

fn assign_one_line(
    region: &mut Region<Fr>,
    config: &HostOpConfig,
    offset: &mut usize,
    operand: Fr,
    opcode: Fr,
    index: Fr,
    merge: Fr,
    ind: Fr,
) -> Result<AssignedCell<Fr, Fr>, Error> {
    let r = config.assign_cell(region, *offset, &HostOpConfig::filtered_operand(), operand)?;
    config.assign_cell(region, *offset, &HostOpConfig::filtered_opcode(), opcode)?;
    config.assign_cell(region, *offset, &HostOpConfig::filtered_index(), index)?;
    config.assign_cell(region, *offset, &HostOpConfig::indicator(), ind)?;
    config.assign_cell(region, *offset, &HostOpConfig::merged_op(), merge)?;
    *offset +=1;
    Ok(r)
}

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

        let entries = shared_operands.iter().zip(shared_opcodes).zip(shared_index);

        let selected_entries = entries.filter(|((_operand, opcode), _index)| {
            opcodes.contains(opcode)
        }).collect::<Vec<_>>();

        let mut offset = 0;

        let mut r = vec![];

        // TODO: Change 8 to RATE ?
        for group in selected_entries.chunks(1+8*4+4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

            let cell = assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
               *operand, Fr::zero())?;
            r.push(Limb::new(Some(cell), *operand));

            let mut reducer = Reduce::new(vec![
                ReduceRule::Field(Fr::zero(), 64),
            ]);
            for &((operand, opcode), index) in group.into_iter().skip(1) {
                reducer.reduce(operand.get_lower_128() as u64);
                let indicator = if reducer.cursor == 0 {
                    Fr::zero()
                } else {
                    vec![0;reducer.cursor].iter().fold(Fr::one(), |acc, _x| {
                        println!("acc");
                        acc * Fr::from_u128(1u128 << 64)
                    })
                };
                println!("reducer value is {:?}, ind is {:?} cursor {}", reducer.rules[0].field_value(), indicator, reducer.cursor);
                if reducer.cursor == 0 {
                    let cell = assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
                        reducer.rules[0].field_value().unwrap(), indicator.clone())?;
                    r.push(Limb::new(Some(cell), reducer.rules[0].field_value().unwrap()));
                } else {
                    assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
                        reducer.rules[0].field_value().unwrap(), indicator.clone())?;
                }
            }
        }
        println!("reducer value {:?}", r.iter().map(|x| x.value).collect::<Vec<_>>());
        Ok(r)
    }
    fn synthesize(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        println!("arg value {:?}", arg_cells.iter().map(|x| x.value).collect::<Vec<_>>());
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

    fn hash_to_host_call_table(inputs: [Fr; 8], result: Fr) -> ExternalHostCallEntryTable {
        let mut r = vec![];
        r.push(hash_cont(true));
        for f in inputs.iter() {
                r.push(crate::adaptor::fr_to_args(*f, 4, 64, PoseidonPush));
        }
        r.push(crate::adaptor::fr_to_args(result, 4, 64, PoseidonFinalize));
        ExternalHostCallEntryTable(r.into_iter().flatten().collect())
    }


    #[test]
    fn generate_poseidon_input() {
        let mut hasher = crate::host::poseidon::gen_hasher();
        let result = hasher.squeeze();
        let table = hash_to_host_call_table(
            [Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()],
            result
        );
        let file = File::create("poseidontest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
