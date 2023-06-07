pub mod bls;
pub mod bn256;
pub mod merkle;
pub mod rmd160;
pub mod modexp;
pub mod poseidon;
pub mod range;

use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

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
