use crate::circuits::{LookupAssistChip, LookupAssistConfig};
use crate::utils::{GateCell, Limb};
use crate::{
    customized_circuits, customized_circuits_expand, item_count, table_item, value_for_assign,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

pub const BIT_XOR: u8 = 1;
pub const BIT_AND: u8 = 2;
pub const BIT_NOT_AND: u8 = 3;
pub const BIT_ROTATE_LEFT: u8 = 4; // 4 + 7, max 11 ---- total 2^4
pub const BIT_ROTATE_RIGHT: u8 = 12; // 12 + 7, max 21 -- total 2^5

// a0 a1 a2 a3
// a4 a5 a6 a7
// b0 b1 b2 b3
// b4 b5 b6 b7
// c0 c1 c2 c3
// c4 c5 c6 c7
// (a0,b0,c0) in lookup_set

#[rustfmt::skip]
customized_circuits!(BitsArithConfig, 1, 0, 4, 0,
   | lhs   |  rhs   |  res   | op
);

impl LookupAssistConfig for BitsArithConfig {
    /// register columns (col) to be XOR checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        cs: &mut ConstraintSystem<F>,
        cols: impl Fn(&mut VirtualCells<F>) -> Vec<Expression<F>>,
    ) {
        for i in 0..4 {
            cs.lookup_any("check bits arith", |meta| {
                let lhs = self.get_expr(meta, BitsArithConfig::lhs());
                let rhs = self.get_expr(meta, BitsArithConfig::rhs());
                let op = self.get_expr(meta, BitsArithConfig::op());
                let res = self.get_expr(meta, BitsArithConfig::res());
                let icols = cols(meta);
                vec![
                    (icols[i].clone(), lhs),
                    (icols[i + 4].clone(), rhs),
                    (icols[i + 8].clone(), res),
                    (icols[12].clone(), op),
                    // add an indicator
                ]
            });
        }
    }
}

pub struct BitsArithChip<F: FieldExt> {
    config: BitsArithConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupAssistChip<F> for BitsArithChip<F> {
    fn provide_lookup_evidence(
        &mut self,
        _region: &mut Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }
}

impl<F: FieldExt> BitsArithChip<F> {
    pub fn new(config: BitsArithConfig) -> Self {
        BitsArithChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> BitsArithConfig {
        let fixed = [0; 4].map(|_| cs.fixed_column());
        let selector = [];

        let config = BitsArithConfig {
            fixed,
            selector,
            witness: [],
        };

        config
    }

    fn assign_table_entries(
        &mut self,
        region: &mut Region<F>,
        opcall: impl Fn(u8, u8) -> u8,
        opcode: u8,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let op = F::from(opcode as u64);
        for i in 0..=u8::MAX {
            for j in 0..=u8::MAX {
                let lhs = F::from(i as u64);
                let rhs = F::from(j as u64);
                let res = F::from(opcall(i, j) as u64);
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::lhs(), lhs)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::rhs(), rhs)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::res(), res)?;
                self.config
                    .assign_cell(region, *offset, &BitsArithConfig::op(), op)?;
                *offset = *offset + 1;
            }
        }
        Ok(())
    }

    /// initialize the table columns that contains every possible result of 8-bit value via XOR or ADD operation
    /// initialize needs to be called before using the BitsArithchip
    pub fn initialize(&mut self, region: &mut Region<F>, offset: &mut usize) -> Result<(), Error> {
        // initialize the XOR table with the encoded value
        self.assign_table_entries(region, |x, y| x ^ y, BIT_XOR, offset)?;
        self.assign_table_entries(region, |x, y| x & y, BIT_AND, offset)?;
        self.assign_table_entries(region, |x, y| (!x) & y, BIT_NOT_AND, offset)?;
        for i in 0..8 {
            self.assign_table_entries(
                region,
                |x, y| {
                    if i != 0 {
                        ((x << i) & 0xff) + (y >> (8 - i))
                    } else {
                        x
                    }
                },
                BIT_ROTATE_LEFT + i,
                offset,
            )?;
        }
        Ok(())
    }
}
