use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
    constant_from,
};
use crate::utils::GateCell;

use std::fmt::Debug;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Fixed, Column, Advice,
    Selector, Expression, VirtualCells,
    Error,
};
use crate::circuits::LookupAssistConfig;
use crate::circuits::LookupAssistChip;
use halo2_proofs::poly::Rotation;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Chip, Region, AssignedCell, Layouter};
use crate::host::ForeignInst;
use crate::host::ForeignInst::{
    PoseidonNew,
    PoseidonPush,
    PoseidonFinalize,
};

use std::marker::PhantomData;

/*
 *
 * 1. lookup_hint start from 0
 * 2. op_hint increase each time an logical oprand is ready
 * 3. only lookup at row where lookup_ind = 0
 * 4.
 * 5. op_hint is the counting number for each opcode
 */

customized_circuits!(HashAdaptorConfig, 2, 6, 1, 1,
   | operand   | opcode   | gindex   | merged_operand | merge_hint   | lookup_ind   | start | sel
   | nil       | opcode_n | gindex_n | nil            | merge_hint_n | lookup_ind_n | nil   | nil
);

impl LookupAssistConfig for HashAdaptorConfig {
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

impl<F:FieldExt> LookupAssistChip<F> for HashAdaptorChip<F> {
    fn provide_lookup_evidence (
        &mut self,
        _region: &mut Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }
}

pub struct HashAdaptorChip<F:FieldExt> {
    config: HashAdaptorConfig,
    offset: usize,
    context: (F, usize, usize), //merged operand, op_hint index, lookup_index
    _marker: PhantomData<F>
}

impl<F: FieldExt> HashAdaptorChip<F> {
    pub fn new(config: HashAdaptorConfig) -> Self {
        HashAdaptorChip {
            config,
            offset:0,
            context: (F::one(), 0, 0),
            _marker: PhantomData,
        }
    }

    pub fn initialize(&mut self, region: &mut Region<F>) -> Result <(), Error> {
        Ok(())
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> HashAdaptorConfig {
        let witness= [0; 6]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 1].map(|_| cs.fixed_column());
        let selector = [cs.selector()];

        let config = HashAdaptorConfig { fixed, selector, witness };
        cs.create_gate("operand feeding point",  |meta| {
            let op = config.get_expr(meta, HashAdaptorConfig::opcode());
            let op_n = config.get_expr(meta, HashAdaptorConfig::opcode_n());
            let merge_hint = config.get_expr(meta, HashAdaptorConfig::merge_hint());
            let merge_hint_n = config.get_expr(meta, HashAdaptorConfig::merge_hint_n());
            let sel = config.get_expr(meta, HashAdaptorConfig::sel());
            vec![
                sel.clone() * (op_n.clone() - op.clone()) * merge_hint.clone(),  // op_hint is zero every time opcode is switched
                sel * (op.clone() - constant_from!(PoseidonNew))
                    * (merge_hint.clone() - constant_from!(3))
                    * (merge_hint_n - merge_hint - constant_from!(1)),
            ]
        });

        // calculate the round index: lookup_ind increase after hint = 3
        cs.create_gate("compute localindex",  |meta| {
            let op_n = config.get_expr(meta, HashAdaptorConfig::opcode_n());
            let lookup_ind = config.get_expr(meta, HashAdaptorConfig::lookup_ind());
            let lookup_ind_n = config.get_expr(meta, HashAdaptorConfig::lookup_ind_n());
            let sel = config.get_expr(meta, HashAdaptorConfig::sel());
            let op = config.get_expr(meta, HashAdaptorConfig::opcode());
            vec![
                sel.clone()
                    * (op_n.clone() - constant_from!(PoseidonNew))
                    * (lookup_ind_n.clone() - lookup_ind.clone()), // op_hint inc in the push block
                sel * (op_n.clone() - constant_from!(PoseidonPush))
                    * (op_n.clone() - constant_from!(PoseidonFinalize))
                    * (lookup_ind_n - lookup_ind - constant_from!(1)) // op_hint inc in the new block

            ]
        });
        config
    }

    fn increase_lookup_index(
        &mut self,
    ) {
        self.context.2 += 1;
    }

    fn merge_operand(
        &mut self,
        operand: F,
    ) {
        if self.context.1 == 4 {
            self.context = (operand, 0, self.context.2);
        } else {
            self.context = (operand, self.context.1+1, self.context.2);
        }
    }

    pub fn assign_op(
        &mut self,
        region: &mut Region<F>,
        opcode: ForeignInst,
        operand: F,
        merged_operand: F,
        index: F,
    ) -> Result<(), Error> {
        self.config.assign_cell(
            region,
            self.offset,
            &HashAdaptorConfig::opcode(),
            F::from(opcode.clone() as u64)
        )?;
        self.config.assign_cell(
            region,
            self.offset,
            &HashAdaptorConfig::operand(),
            operand,
        )?;
        self.config.assign_cell(
            region,
            self.offset,
            &HashAdaptorConfig::gindex(),
            index,
        )?;
        match opcode {
            PoseidonNew => {
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merge_hint(),
                    F::zero()
                )?;
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merged_operand(),
                    merged_operand
                )?;
                self.increase_lookup_index();
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::lookup_ind(),
                    F::from(self.context.2 as u64), // lookupindex never change
                )?;

            },
            PoseidonPush => {
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merge_hint(),
                    F::from(self.context.1 as u64)
                )?;
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merged_operand(),
                    merged_operand
                )?;
                self.merge_operand(merged_operand);
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::lookup_ind(),
                    F::from(self.context.2 as u64), // lookupindex never change
                )?;

            },
            PoseidonFinalize => {
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merge_hint(),
                    F::from(self.context.1 as u64)
                )?;
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::merged_operand(),
                    merged_operand
                )?;
                self.merge_operand(merged_operand);
                self.config.assign_cell(
                    region,
                    self.offset,
                    &HashAdaptorConfig::lookup_ind(),
                    F::from(self.context.2 as u64), // lookupindex never change
                )?;
            },
            _ => {
                ()
            }
        };
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use crate::adaptor::hashadaptor::{
        HashAdaptorConfig,
        HashAdaptorChip,
    };
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
        hashadaptorconfig: HashAdaptorConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let hashadaptorconfig = HashAdaptorChip::<Fr>::configure(meta);
            Self::Config {
               hashadaptorconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let mut adaptorchip = HashAdaptorChip::<Fr>::new(config.clone().hashadaptorconfig);
            layouter.assign_region(
                || "assign poseidon test",
                |mut region| {
                    adaptorchip.initialize(&mut region)?;
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
