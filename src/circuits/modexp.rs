use crate::utils::GateCell;
use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
};
use std::ops::{Mul, Div};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region, AssignedCell},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use std::ops::{Shr, Shl};
use crate::constant;
use num_bigint::BigUint;

/*
 * Customized gates for modexp
 */
customized_circuits!(ModExpConfig, 2, 5, 7, 1,
   | l0  | l1   | l2  | l3  | d   |  c0  | c1  | c2  | c3  | c   | c03  | c12  | sel
   | nil | nil  | nil | nil | d_n |  nil | nil | nil | nil | nil | nil  | nil  | nil
);
pub struct ModExpChip<F:FieldExt> {
    config: ModExpConfig,
    _marker: PhantomData<F>
}

#[derive(Clone, Debug)]
pub struct Limb<F: FieldExt> {
    cell: Option<AssignedCell<F, F>>,
    value: F
}

impl<F: FieldExt> Limb<F> {
    fn new(cell: Option<AssignedCell>, value: F) -> Self {
        Limb { cell, value }
    }
}

pub struct Number<F: FieldExt> {
    limbs: [Limb<F>; 4],
    native: F,
}

fn limbs_to_bn<F: FieldExt>(limbs: &Vec<Limb<F>>) -> BigUint {
    todo!()
}

fn bn_to_limbs<F: FieldExt>(bn: &BigUint) -> Number<F> {
    todo!()
}


impl<F: FieldExt> Chip<F> for ModExpChip<F> {
    type Config = ModExpConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ModExpChip<F> {
    pub fn new(config: ModExpConfig) -> Self {
        ModExpChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> ModExpConfig {
        let witness= [0; 5]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 7].map(|_| cs.fixed_column());
        let selector =[cs.selector()];

        let config = ModExpConfig { fixed, selector, witness };

        cs.create_gate("select left right", |meta| {
            let l0 = config.get_expr(meta, ModExpConfig::l0());
            let l1 = config.get_expr(meta, ModExpConfig::l1());
            let l2 = config.get_expr(meta, ModExpConfig::l2());
            let l3 = config.get_expr(meta, ModExpConfig::l3());
            let d = config.get_expr(meta, ModExpConfig::d());
            let dnext = config.get_expr(meta, ModExpConfig::d_n());
            let c0 = config.get_expr(meta, ModExpConfig::c0());
            let c1 = config.get_expr(meta, ModExpConfig::c1());
            let c2 = config.get_expr(meta, ModExpConfig::c2());
            let c3 = config.get_expr(meta, ModExpConfig::c3());
            let c  = config.get_expr(meta, ModExpConfig::c());
            let c03 = config.get_expr(meta, ModExpConfig::c03());
            let c12  = config.get_expr(meta, ModExpConfig::c12());
            let sel = config.get_expr(meta, ModExpConfig::sel());

            // if odd then carry is put at right else put at left
            vec![
                sel * (
                    l0.clone() * c0
                +   l1.clone() * c1
                +   l2.clone() * c2
                +   l3.clone() * c3
                +   d  * c
                +   l0 * l3 * c03
                +   l1 * l2 * c12
                +   dnext)
            ]

        });
        config
    }

    pub fn assign_number (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        todo!()
    }

    fn assign_line (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       value:  [Option<Limb<F>>; 6],
       coeffs: [Option<F>; 7],
    ) -> Result<Vec<Limb<F>>, Error> {
        let witnesses = [
            ModExpConfig::l0(),
            ModExpConfig::l1(),
            ModExpConfig::l2(),
            ModExpConfig::l3(),
            ModExpConfig::d(),
            ModExpConfig::d_n(),
        ];
        let coeffs = [
            ModExpConfig::c0(),
            ModExpConfig::c1(),
            ModExpConfig::c2(),
            ModExpConfig::c3(),
            ModExpConfig::c(),
            ModExpConfig::c03(),
            ModExpConfig::c12(),
        ];
        let mut limbs = vec![];
        for i in 0..6 {
            value[i].clone().map(|x| {
                let cell = self.config.assign_cell(region, *offset, witnesses[i], x.value).unwrap();
                limbs.push(Limb::new(Some(cell), value[i]));
                x.cell.map(|c| {
                    region.constrain_equal(cell.cell(), c.cell()).unwrap();
                });
            });
        }
        for i in 0..7 {
            coeffs[i].clone().map(|x| {
                let cell = self.config.assign_cell(region, *offset, coeffs[i], x.value).unwrap();
            });
        }
        offset = offset+1;
        Ok(limbs)
    }


    pub fn assign_add (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
        /*
        for i in 0..5 {
            let v = lhs.lim
            let l = self.assign_line(region, offset, vec![lhs.limbs[0], rhs.limbs[0], None, None, None, 
        }
        */
       /* assign all x0..x3 and y0..y3 */
       //self.config.assign_cell(region, *offset, ModExpConfig::x0(), *lhs.limbs[0].cell.value().unwrap())?;
       /* assign all sum0 - sum3 */
       /*
       let sum_0 = *lhs.limbs[0].cell.value().unwrap() + *rhs.limbs[0].cell.value().unwrap();
       let sum_limbs_0 = self.config.assign_cell(region, *offset+1, ModExpConfig::x0_n(), sum_0)?;
       let sum_limbs_1 = self.config.assign_cell(region, *offset+1, ModExpConfig::x0_n(), sum_0)?;
       let sum_limbs_2 = self.config.assign_cell(region, *offset+1, ModExpConfig::x0_n(), sum_0)?;
       let sum_limbs_3 = self.config.assign_cell(region, *offset+1, ModExpConfig::x0_n(), sum_0)?;
       self.config.enable_selector(region, *offset, ModExpConfig::sel())?;
       Ok(Number {
           limbs: [
               Limb {cell: sum_limbs_0},
               Limb {cell: sum_limbs_1},
               Limb {cell: sum_limbs_2},
               Limb {cell: sum_limbs_3},
           ],
           native: F::one() //fake
       })
       */
       todo!()
    }

    pub fn mod_power108m1 (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        todo!();
    }

    pub fn mod_power216 (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        todo!()
    }


    pub fn mod_power108m1_mul (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        todo!();
    }

    pub fn mod_power216_mul (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        todo!()
    }

    pub fn mod_power108m1_zero(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        todo!()
    }

    pub fn mod_power216_zero(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        todo!()
    }


    pub fn assign_mod_mult(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
       modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let bn_lhs = limbs_to_bn(&lhs.limbs.to_vec());
        let bn_rhs = limbs_to_bn(&rhs.limbs.to_vec());
        let bn_mult = bn_lhs.mul(bn_rhs);
        let bn_modulus = limbs_to_bn(&modulus.limbs.to_vec());
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone());
        let bn_rem = bn_mult.min(bn_quotient.clone() * bn_modulus.clone());
        let modulus = self.assign_number(region, offset, bn_to_limbs(&bn_modulus))?;
        let rem = self.assign_number(region, offset, bn_to_limbs(&bn_rem))?;
        let quotient = self.assign_number(region, offset, bn_to_limbs(&bn_quotient))?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, offset, lhs, rhs)?;
        let mod_108m1_rhs = self.mod_power108m1_mul(region, offset, &quotient, &modulus)?;
        let mod_108m1_rem = self.mod_power108m1(region, offset, &rem)?;
        self.mod_power108m1_zero(
            region,
            offset,
            vec![mod_108m1_lhs.clone(), mod_108m1_rhs.clone(), mod_108m1_rem.clone()],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, offset, lhs, rhs)?;
        let mod_216_rhs = self.mod_power216_mul(region, offset, &quotient, &modulus)?;
        let mod_216_rem = self.mod_power216(region, offset, &rem)?;
        self.mod_power216_zero(
            region,
            offset,
            vec![mod_108m1_lhs, mod_108m1_rhs, mod_108m1_rem],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        Ok(rem)
    }


    pub fn square_mod(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       square: &Number<F>,
       divisor: &Number<F>
    ) -> Result <Number<F>, Error> {
        // result = ???
        // square * square = k * divisor + result
        //let mod_128;
        //Ok(result)
        todo!();
    }
}
