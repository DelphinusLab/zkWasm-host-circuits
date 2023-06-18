pub mod bls;
pub mod bn256;
pub mod merkle;
pub mod rmd160;
pub mod modexp;
pub mod poseidon;
pub mod range;

use halo2_proofs::pairing::bn256::Fr;
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
};

use crate::circuits::range::{
    RangeCheckConfig,
    RangeCheckChip,
};

use std::ops::{Mul, Div};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region, AssignedCell, Layouter},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;



pub trait HostOpSelector {
    type Config: Clone + std::fmt::Debug;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
    ) -> Self::Config;
    fn construct(c: Self::Config) -> Self;
    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error>;
    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error>;
}

/*
 * Customized gates for modexp
 */
customized_circuits!(CommonGateConfig, 2, 5, 11, 1,
   | l0  | l1   | l2  | l3  | d   |  c0  | c1  | c2  | c3  | cd  | cdn | c   | c03  | c12  | range | check_range | sel
   | nil | nil  | nil | nil | d_n |  nil | nil | nil | nil | nil | nil | nil | nil  | nil  | nil   | nil         | nil
);

#[derive(Clone, Debug)]
pub struct Limb<F: FieldExt> {
    cell: Option<AssignedCell<F, F>>,
    value: F
}

impl<F: FieldExt> Limb<F> {
    fn new(cell: Option<AssignedCell<F, F>>, value: F) -> Self {
        Limb { cell, value }
    }
}

impl CommonGateConfig {
    pub fn configure<F:FieldExt> (cs: &mut ConstraintSystem<F>, range_check_config: &RangeCheckConfig) -> Self {
        let witness= [0; 5]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 11].map(|_| cs.fixed_column());
        let selector =[cs.selector()];

        let config = CommonGateConfig { fixed, selector, witness };

        range_check_config.register(
            cs,
            |c| config.get_expr(c, CommonGateConfig::l0()) * config.get_expr(c, CommonGateConfig::check_range()),
            |c| config.get_expr(c, CommonGateConfig::range()),
        );

        cs.create_gate("one line constraint", |meta| {


            let l0 = config.get_expr(meta, CommonGateConfig::l0());
            let l1 = config.get_expr(meta, CommonGateConfig::l1());
            let l2 = config.get_expr(meta, CommonGateConfig::l2());
            let l3 = config.get_expr(meta, CommonGateConfig::l3());
            let d = config.get_expr(meta, CommonGateConfig::d());
            let dnext = config.get_expr(meta, CommonGateConfig::d_n());
            let c0 = config.get_expr(meta, CommonGateConfig::c0());
            let c1 = config.get_expr(meta, CommonGateConfig::c1());
            let c2 = config.get_expr(meta, CommonGateConfig::c2());
            let c3 = config.get_expr(meta, CommonGateConfig::c3());
            let c  = config.get_expr(meta, CommonGateConfig::c());
            let cd  = config.get_expr(meta, CommonGateConfig::cd());
            let cdn  = config.get_expr(meta, CommonGateConfig::cdn());
            let c03 = config.get_expr(meta, CommonGateConfig::c03());
            let c12  = config.get_expr(meta, CommonGateConfig::c12());
            let sel = config.get_expr(meta, CommonGateConfig::sel());

            // if odd then carry is put at right else put at left
            vec![
                sel * (
                    l0.clone() * c0
                +   l1.clone() * c1
                +   l2.clone() * c2
                +   l3.clone() * c3
                +   d  * cd
                +   dnext * cdn
                +   l0 * l3 * c03
                +   l1 * l2 * c12
                +   c)
            ]

        });

        config
    }


    fn assign_line<F:FieldExt> (
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       value:  [Option<Limb<F>>; 6],
       coeffs: [Option<F>; 9],
       limbbound: usize, // the boundary limit of the first cell
    ) -> Result<Vec<Limb<F>>, Error> {
        let ws = value.clone().to_vec().iter()
            .map(|x|x.clone().map_or(F::zero(), |x| x.value))
            .collect::<Vec<F>>();
        let cs = coeffs.clone().to_vec().iter().map(|x| x.map_or(F::zero(), |x| x)).collect::<Vec<F>>();
        assert!(
            ws[0] * cs[0]
            + ws[1] * cs[1]
            + ws[2] * cs[2]
            + ws[3] * cs[3]
            + ws[4] * cs[4]
            + ws[5] * cs[5]
            + ws[0] * ws[3] * cs[6]
            + ws[1] * ws[2] * cs[7]
            + cs[8] == F::zero()
        );

        let witnesses = [
            CommonGateConfig::l0(),
            CommonGateConfig::l1(),
            CommonGateConfig::l2(),
            CommonGateConfig::l3(),
            CommonGateConfig::d(),
            CommonGateConfig::d_n(),
        ];
        let cs = [
            CommonGateConfig::c0(),
            CommonGateConfig::c1(),
            CommonGateConfig::c2(),
            CommonGateConfig::c3(),
            CommonGateConfig::cd(),
            CommonGateConfig::cdn(),
            CommonGateConfig::c03(),
            CommonGateConfig::c12(),
            CommonGateConfig::c(),
        ];


        let mut limbs = vec![];
        for i in 0..6 {
            let v = value[i].as_ref().map_or(F::zero(), |x| x.value);
            let cell = self.assign_cell(region, *offset, &witnesses[i], v).unwrap();
            value[i].clone().map(|x| {
                limbs.push(Limb::new(Some(cell.clone()), x.value));
                x.cell.map(|c| {
                    region.constrain_equal(cell.cell(), c.cell()).unwrap();
                });
            });
        }
        for i in 0..9 {
            let v = coeffs[i].as_ref().map_or(F::zero(), |x| *x);
            self.assign_cell(region, *offset, &cs[i], v).unwrap();
        }
        self.enable_selector(region, *offset, &CommonGateConfig::sel())?;
        self.assign_cell(region, *offset, &CommonGateConfig::range(), F::from(limbbound as u64))?;
        self.assign_cell(region, *offset, &CommonGateConfig::check_range(), F::from(
            if limbbound == 0 {0u64} else {1u64}
        ))?;

        if limbbound != 0 {
            range_check_chip.assign_value_with_range(region, value[0].as_ref().unwrap().value, limbbound)?;
        };

        *offset = *offset+1;
        Ok(limbs)
    }
}



