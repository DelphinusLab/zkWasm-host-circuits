use std::fmt::Debug;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{VirtualCells, Error, Expression};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Chip, Region, AssignedCell, Layouter};
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
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            Fr::from(ForeignInst::PoseidonNew as u64),
            Fr::from(ForeignInst::PoseidonPush as u64),
            Fr::from(ForeignInst::PoseidonFinalize as u64),
        ];

        let entries = shared_operands.iter().zip(shared_opcodes).zip(shared_index);

        let selected_entries = entries.filter(|((operand, opcode), index)| {
            opcodes.contains(opcode)
        }).collect::<Vec<_>>();

        let mut offset = 0;

        let mut r = vec![];

        for group in selected_entries.chunks(1+8*4+4) {
            let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            assert!(opcode.clone() == Fr::from(PoseidonNew as u64));

            r.push(assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
               *operand, Fr::zero())?);

            let operands = group.iter().skip(1).collect::<Vec<_>>().chunks(4);
            let mut reducer = Reduce::new(vec![
                ReduceRule::Field(Fr::zero(), 64),
            ]);
            let mut indicator = Fr::from_u128(1u128 << 64);
            for &((operand, opcode), index) in group.into_iter().skip(1) {
                reducer.reduce(operand.get_lower_128() as u64);
                if reducer.cursor == 0 {
                    //reducer.reset(0);
                    r.push(assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
                                         reducer.rules[0].field_value().unwrap(), Fr::zero())?);
                } else {
                    r.push(assign_one_line(region, config, &mut offset, *operand, *opcode, *index,
                                         reducer.rules[0].field_value().unwrap(), indicator.clone())?);
                }
            }
        }
        Ok(vec![])
    }
    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let a = arg_cells[0..9].to_vec();
        let b = arg_cells[9..26].to_vec();
        let ab = arg_cells[26..74].to_vec();
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;
    use crate::host::{
        ExternalHostCallEntryTable,
        ExternalHostCallEntry,
    };

    use crate::host::ForeignInst;
    use crate::host::ForeignInst::{
        PoseidonNew,
        PoseidonPush,
        PoseidonFinalize,
    };


    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    #[derive(Debug, Default)]
    struct TestCircuit {
        table: ExternalHostCallEntryTable,
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        poseidon_config: CommonGateConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let poseidon_config = CommonGateConfig::configure(meta, &());
            Self::Config {
                poseidon_config
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "assign poseidon test",
                |mut region| {
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    fn hash_cont(restart: bool) -> Vec<ExternalHostCallEntry> {
        vec![ExternalHostCallEntry {
            op: ForeignInst::PoseidonNew as usize,
            value: if restart {1u64} else {0u64},
            is_ret: false,
        }]

    }

    fn hash_to_host_call_table(inputs: Vec<Fr>) -> ExternalHostCallEntryTable {
        let mut r = vec![];
        for (i, chunk) in inputs.chunks(8).enumerate() {
            r.push(hash_cont(i==0));
            for f in chunk.iter() {
                r.push(crate::adaptor::fr_to_args(*f, 4, 64, PoseidonPush));
            }
        }
        r.push(crate::adaptor::fr_to_args(Fr::one(), 4, 64, PoseidonFinalize));
        ExternalHostCallEntryTable(r.into_iter().flatten().collect())
    }


    #[test]
    fn test_poseidon_adapor_circuit_00() {
        let mut hasher = crate::host::poseidon::gen_hasher();
        let result = hasher.squeeze();
        let table = hash_to_host_call_table(vec![Fr::one(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero()]);
        let test_circuit = TestCircuit {table};
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
