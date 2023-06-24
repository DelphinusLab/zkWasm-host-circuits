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

use std::marker::PhantomData;

/* Given a merkel tree eg1 with height=3:
 *
 */

customized_circuits!(HashAdaptorConfig, 2, 2, 0, 0,
   | carry   | input
   | carry_n | nil
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
    _marker: PhantomData<F>
}

impl<F: FieldExt> HashAdaptorChip<F> {
    pub fn new(config: HashAdaptorConfig) -> Self {
        HashAdaptorChip {
            config,
            offset:0,
            _marker: PhantomData,
        }
    }

    pub fn initialize(&mut self, region: &mut Region<F>) -> Result <(), Error> {
        Ok(())
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> HashAdaptorConfig {
        let witness= [0; 2]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        //let fixed = [0; 2].map(|_| cs.fixed_column());
        let fixed = [];
        let selector =[];

        let config = HashAdaptorConfig { fixed, selector, witness };
        config
    }
}
