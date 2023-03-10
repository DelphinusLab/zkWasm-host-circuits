pub mod bls;
pub mod merkle;

use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Fixed, Column, Error, ConstraintSystem}
};
use halo2ecc_s::circuit::{
    base_chip::{BaseChip, BaseChipConfig},
    range_chip::{RangeChip, RangeChipConfig},
};

pub trait HostOpSelector {
    type Config: Clone + std::fmt::Debug;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        base_config: &BaseChipConfig,
        range_config: &RangeChipConfig
    ) -> Self::Config;
    fn construct(c: Self::Config) -> Self;
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
    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error>;
}


