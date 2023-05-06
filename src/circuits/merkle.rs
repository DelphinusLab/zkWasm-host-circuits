use crate::customized_curcuits;
use crate::table_item;
use crate::item_count;
use crate::utils::GateCell;
use halo2_proofs::arithmetic::FieldExt;
use std::marker::PhantomData;
use halo2_proofs::plonk::{Fixed, Column, Advice, Selector, Expression, VirtualCells};
use halo2_proofs::poly::Rotation;

customized_curcuits!(MerkleConfig, 1, 10, 5, 0, 0,
    | carry | trace | hash | index | pos | more
);


pub struct MerkleChip<F:FieldExt> {
    config: MerkleConfig,
    _marker: PhantomData<F>
}

impl MerkleConfig {
    fn get_expr<F:FieldExt>(&self, meta: &mut VirtualCells<F>, gate_cell: GateCell) -> Expression<F> {
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
}
