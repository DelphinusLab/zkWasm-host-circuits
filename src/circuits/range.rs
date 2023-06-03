use crate::utils::{
    GateCell,
    field_to_bn,
    bn_to_field,
};
use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
    constant_from,
};
use std::ops::{Mul, Div};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region, AssignedCell},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;

/*
 * Customized gates range_check(target)
 * limbs \in table
 * sum limbs * acc will be the sum of the target
 */
customized_circuits!(RangeCheckConfig, 2, 3, 2, 0,
   | limb   |  acc   | rem   | table | sel 
   | limb_n |  acc_n | rem_n | nil   | sel_n
);

pub struct RangeCheckChip<F:FieldExt> {
    config: RangeCheckConfig,
    _marker: PhantomData<F>
}


impl<F: FieldExt> RangeCheckChip<F> {
    pub fn new(config: RangeCheckConfig) -> Self {
        RangeCheckChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> RangeCheckConfig {
        let witness= [0; 3]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 2].map(|_| cs.fixed_column());
        let selector =[];

        let config = RangeCheckConfig { fixed, selector, witness };

        // Range Check of all limbs
        cs.lookup_any("within ranges", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let table = config.get_expr(meta, RangeCheckConfig::table());
            vec![(limb, table)]
        });



        // First we require the rem is continus if it is not zero
        cs.create_gate("range check constraint", |meta| {
            let rem = config.get_expr(meta, RangeCheckConfig::rem());
            let rem_n = config.get_expr(meta, RangeCheckConfig::rem_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());

            vec![
                sel * rem.clone() * (rem - rem_n - constant_from!(1))
            ]

        });

        // Second we make sure if the rem is not zero then
        // carry = carry_n * 2^12 + limb
        // for example, suppose we have range check with 5 limb
        // | a_0 | carry_0 | 5 | 1 |
        // | a_1 | carry_1 | 4 | 1 |
        // | a_2 | carry_2 | 3 | 1 |
        // | a_3 | carry_3 | 2 | 1 |
        // | a_4 | carry_4 | 1 | 1 |
        // | nil | 0       | 0 | 0 |
        cs.create_gate("limb acc constraint", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let limb_n = config.get_expr(meta, RangeCheckConfig::limb_n());
            let acc = config.get_expr(meta, RangeCheckConfig::acc());
            let acc_n = config.get_expr(meta, RangeCheckConfig::acc_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());
            let sel_n = config.get_expr(meta, RangeCheckConfig::sel_n());

            vec![
                sel * (acc - limb - acc_n * constant_from!(2u64<<12) * sel_n)
            ]

        });
        config
    }
}

 



