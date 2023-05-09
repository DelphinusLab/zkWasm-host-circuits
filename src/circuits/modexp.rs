use crate::utils::GateCell;
use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
};

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


///
/// x0, x1, x2, x3 op y0, y1, y2, y3
///
customized_circuits!(ModExpConfig, 2, 10, 1, 1,
   | x0   | x1   | x2   | x3   | xr   | y0 | y1 | y2 | y3 | yr | c  | cp | cm |sel
   | x0_n | x1_n | x2_n | x3_n | xr_n | nil| nil| nil| nil| nil| nil| nil| nil|nil
);
pub struct ModExpChip<F:FieldExt> {
    config: ModExpConfig,
    _marker: PhantomData<F>
}

pub struct Limb<F: FieldExt> {
    cell: AssignedCell<F, F>
}

pub struct Number<F: FieldExt> {
    limbs: [Limb<F>; 4],
    native: F,
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
        let witness= [0; 10]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [cs.fixed_column()];
        let selector =[cs.selector()];

        let config = ModExpConfig { fixed, selector, witness };

        cs.create_gate("select left right", |meta| {
            let x0 = config.get_expr(meta, ModExpConfig::x0());
            let x1 = config.get_expr(meta, ModExpConfig::x1());
            let x2 = config.get_expr(meta, ModExpConfig::x2());
            let x3 = config.get_expr(meta, ModExpConfig::x3());
            let y0 = config.get_expr(meta, ModExpConfig::y0());
            let y1 = config.get_expr(meta, ModExpConfig::y1());
            let y2 = config.get_expr(meta, ModExpConfig::y2());
            let y3 = config.get_expr(meta, ModExpConfig::y3());
            let x0_n = config.get_expr(meta, ModExpConfig::x0_n());
            let x1_n = config.get_expr(meta, ModExpConfig::x1_n());
            let x2_n = config.get_expr(meta, ModExpConfig::x2_n());
            let x3_n = config.get_expr(meta, ModExpConfig::x3_n());
            let sel = config.get_expr(meta, ModExpConfig::sel());
            let cp = config.get_expr(meta, ModExpConfig::cp());


            // if odd then carry is put at right else put at left
            vec![
                sel.clone() * (x0_n - (x0 + y0 + cm*x0*y0 + c) * cp.clone(),
            ]

        });
        config
    }

    pub fn assign_add(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
       /* assign all x0..x3 and y0..y3 */
       self.config.assign_cell(region, *offset, ModExpConfig::x0(), *lhs.limbs[0].cell.value().unwrap())?;
       /* assign all sum0 - sum3 */
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
    }

    pub fn mod_power64(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
    }

    pub fn mod_power128minus1_single(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
    }

    pub fn mod_power128puls1_single(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
    }

    pub fn mod_power128minus1_bop(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       square: &Number<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
    }

    pub fn mod_power128puls1(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        todo!()
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


