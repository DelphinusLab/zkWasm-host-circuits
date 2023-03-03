pub mod bls;
pub mod merkle;

use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Fixed, Column, Error}
};

pub trait HostOpSelector {
    fn assign(
        layouter: &mut impl Layouter<Fr>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
        offset: &mut usize,
        args: [Fr; 3],
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error>;
}


