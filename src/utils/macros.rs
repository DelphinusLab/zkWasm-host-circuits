#[macro_export]
macro_rules! constant_from {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant(F::from($x as u64))
    };
}

#[macro_export]
macro_rules! constant_from_bn {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant(bn_to_field($x))
    };
}

#[macro_export]
macro_rules! constant {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant($x)
    };
}

#[macro_export]
macro_rules! value_for_assign {
    ($x: expr) => {
        Ok($x)
    };
}

#[macro_export]
macro_rules! item_count {
    () => {0usize};
    ($cut:tt nil $($tail:tt)*) => {1usize + item_count!($($tail)*)};
    ($cut:tt $name:tt $($tail:tt)*) => {1usize + item_count!($($tail)*)};
}

#[macro_export]
macro_rules! table_item {
    ($row:expr, $col:expr, ) => {};
    ($row:expr, $col:expr, | nil $($tail:tt)*) => {
        table_item!($row, $col, $($tail)*);
    };
    ($row:expr, $col:expr, | $name:tt $($tail:tt)*) => {
        pub fn $name() -> GateCell {
            let index = $row * $col - 1usize - (item_count!($($tail)*));
            GateCell {
                cell: [Self::typ(index), Self::col(index), Self::row(index)],
                name: String::from(stringify!($name)),
            }
        }
        table_item!($row, $col, $($tail)*);
    };
}

#[macro_export]
macro_rules! customized_circuits_expand {
    ($name:ident, $row:expr, $col:expr, $adv:expr, $fix:expr, $sel:expr, $($item:tt)* ) => {
        #[allow(dead_code)]
        #[derive(Clone, Debug)]
        pub struct $name {
             witness: [Column<Advice>; $adv],
             selector: [Selector; $sel],
             fixed: [Column<Fixed>; $fix],
        }

        impl $name {
            pub fn new(witness: [Column<Advice>; $adv], fixed: [Column<Fixed>; $fix], selector: [Selector; $sel]) -> Self {
                $name {
                    witness,
                    fixed,
                    selector,
                }
            }

            pub fn get_expr<F:FieldExt>(&self, meta: &mut VirtualCells<F>, gate_cell: GateCell) -> Expression<F> {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 0 { // advice
                    meta.query_advice(self.witness[cell[1]], Rotation(cell[2] as i32))
                } else if cell[0] == 1 { // fix
                    meta.query_fixed(self.fixed[cell[1]], Rotation(cell[2] as i32))
                } else { // selector
                    meta.query_selector(self.selector[cell[1]])
                }
            }

            pub fn get_expr_with_offset<F:FieldExt>(&self, meta: &mut VirtualCells<F>, gate_cell: GateCell, offset: usize) -> Expression<F> {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 0 { // advice
                    meta.query_advice(self.witness[cell[1]], Rotation((cell[2] + offset) as i32))
                } else if cell[0] == 1 { // fix
                    meta.query_fixed(self.fixed[cell[1]], Rotation((cell[2] + offset) as i32))
                } else { // selector
                    meta.query_selector(self.selector[cell[1]])
                }
            }

            pub fn get_advice_column(&self, gate_cell: GateCell) -> Column<Advice> {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 0 { // advice
                    self.witness[cell[1]]
                } else {
                    unreachable!();
                }
            }

            pub fn get_fixed_column(&self, gate_cell: GateCell) -> Column<Fixed> {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 1 { // advice
                    self.fixed[cell[1]]
                } else {
                    unreachable!();
                }
            }

            pub fn get_selector_column(&self, gate_cell: GateCell) -> Selector {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 2 { // advice
                    self.selector[cell[1]]
                } else {
                    unreachable!();
                }
            }

            pub fn assign_cell<F:FieldExt>(
                &self,
                region: &mut Region<F>,
                start_offset: usize,
                gate_cell: &GateCell,
                value: F,
            ) -> Result<Limb<F>, Error> {
                let cell = gate_cell.cell;
                //println!("Assign Cell at {} {} {:?}", start_offset, gate_cell.name, value);
                if cell[0] == 0 { // advice
                    let c = region.assign_advice(
                        || gate_cell.name.clone(),
                        self.witness[cell[1]],
                        start_offset + cell[2],
                        || value_for_assign!(value)
                    )?;
                    Ok(Limb::new(Some(c), value))
                } else if cell[0] == 1 { // fix
                    let c = region.assign_fixed(
                        || format!("assign cell"),
                        self.fixed[cell[1]],
                        start_offset + cell[2],
                        || value_for_assign!(value)
                    )?;
                    Ok(Limb::new(Some(c), value))
                } else { // selector
                    unreachable!()
                }
            }

            pub fn bind_cell<F:FieldExt>(
                &self,
                region: &mut Region<F>,
                start_offset: usize,
                cell: &GateCell,
                value: &Limb<F>,
            ) -> Result<Limb<F>, Error> {
                let limb = self.assign_cell(region, start_offset, cell, value.value.clone())?;
                value.cell.as_ref().map(|value| region.constrain_equal(limb.get_the_cell().cell(), value.cell()));
                Ok(limb)
            }


            pub fn enable_selector<F:FieldExt>(
                &self,
                region: &mut Region<F>,
                start_offset: usize,
                gate_cell: &GateCell,
            ) -> Result<(), Error> {
                assert!(gate_cell.cell[0] == 2);
                self.selector[gate_cell.cell[1]].enable(region, start_offset + gate_cell.cell[2])
            }
        }

        impl $name {
            fn typ(index: usize) -> usize {
                let x = index % $col;
                if x < $adv {
                    0
                } else if x < $adv + $fix {
                    1
                } else {
                    2
                }
            }

            fn col(index: usize) -> usize {
                let x = index % $col;
                if x < $adv {
                    x
                } else if x < $adv + $fix {
                    x - $adv
                } else {
                    x - $adv - $fix
                }
            }

            fn row(index: usize) -> usize {
                index / $col
            }

            table_item!($row, $col, $($item)*);
        }
    };
}

#[macro_export]
/// Define customize circuits with (nb_row, nb_adv, nb_fix, nb_expr)
/// | adv    | fix    | sel    |
/// | a      | b      | c      |
/// | a_next | b_next | c_next |
macro_rules! customized_circuits {
    ($name:ident, $row:expr, $adv:expr, $fix:expr, $sel:expr, $($item:tt)* ) => {
        customized_circuits_expand!($name, $row, ($fix + $sel + $adv), $adv, $fix, $sel, $($item)*);
    };
}

#[cfg(test)]
mod tests {
    /*
    use crate::customized_circuits;
    use crate::customized_circuits_expand;
    use crate::table_item;
    use crate::item_count;
    use crate::utils::GateCell;
    use crate::utils::Limb;
    use halo2_proofs::arithmetic::FieldExt;
    use halo2_proofs::plonk::{
        Fixed, Column, Advice,
        Selector, Expression, VirtualCells,
        Error,
    };
    use halo2_proofs::poly::Rotation;

    #[rustfmt::skip]
    customized_circuits!(TestConfig, 2, 2, 1, 1,
        | wc  | b2 | c2 |  d2
        | w1  | b3 | c3 |  d3
    );
    #[test]
    fn test_gate_macro() {
          //let config = TestConfig {};
          //assert_eq!(r.to_vec(), r1);
    }
    */
}
