mod utils;
mod circuits;

use std::marker::PhantomData;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
    pairing::bls12_381::{G1Affine, G2Affine, G1, G2}
};

trait HostCircuit<F: FieldExt>: Clone {
    fn load_shared_operands(
        &self,
        layouter: impl Layouter<F>,
        a: Vec<F>
    ) -> Result<Self, Error>;
    fn filter(
        &self,
        layouter: impl Layouter<F>,
    ) -> Result<Self, Error>;
}

#[derive(Clone, Debug)]
struct SharedOpInfo {
}

// ANCHOR: add-config
#[derive(Clone, Debug)]
struct HostOpConfig {
    shared_operands: Column<Advice>,
    shared_opcodes: Column<Advice>,
    shared_index: Column<Advice>,
    filtered_operands: Column<Advice>,
    filtered_opcodes: Column<Advice>,
    filtered_index: Column<Advice>,
}

struct HostOpChip<F: FieldExt> {
    config: HostOpConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for HostOpChip<F> {
    type Config = HostOpConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> HostOpChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        shared_operands: Column<Advice>,
        shared_opcodes: Column<Advice>,
        shared_index: Column<Advice>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        opcode: F,
    ) -> <Self as Chip<F>>::Config {
        meta.lookup_any("filter-shared-ops", |meta| {
            let sopc = meta.query_advice(shared_opcodes, Rotation::cur());
            let soper = meta.query_advice(shared_operands, Rotation::cur());
            let sidx = meta.query_advice(shared_index, Rotation::cur());
            let foper = meta.query_advice(filtered_operands, Rotation::cur());
            let fopc  = meta.query_advice(filtered_opcodes, Rotation::cur());
            let fidx = meta.query_advice(filtered_index, Rotation::cur());
            vec![(fidx, sidx), (foper, soper), (fopc, sopc)]
        });

        HostOpConfig {
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index
        }
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        shared_operands: &Vec<F>,
        shared_opcodes: &Vec<F>,
        shared_index: &Vec<F>,
        target_opcode: F,
    ) -> Result<(), Error>  {
        layouter.assign_region(
            || "filter operands and opcodes",
            |mut region| {
                println!("asign_region");
                let mut offset = 0;
                let mut picked_offset = 0;
                for opcode in shared_opcodes {
                    println!("opcode is {:?}", opcode);
                    region.assign_advice(
                        || "shared opcodes",
                        self.config.shared_opcodes,
                        offset,
                        || Ok(opcode.clone())
                    )?;
                    region.assign_advice(
                        || "shared operands",
                        self.config.shared_operands,
                        offset,
                        || Ok(shared_operands[offset])
                    )?;
                    region.assign_advice(
                        || "shared index",
                        self.config.shared_index,
                        offset,
                        || Ok(shared_index[offset])
                    )?;
                    if opcode.clone() == target_opcode {
                        region.assign_advice(
                            || "picked operands",
                            self.config.filtered_operands,
                            picked_offset,
                            || Ok(shared_operands[offset])
                        )?;
                        region.assign_advice(
                            || "picked opcodes",
                            self.config.filtered_opcodes,
                            picked_offset,
                            || Ok(target_opcode)
                        )?;

                        region.assign_advice(
                            || "picked index",
                            self.config.filtered_index,
                            picked_offset,
                            || Ok(shared_index[offset])
                        )?;
                        picked_offset += 1;
                    };
                    offset += 1;
                };
                println!("picked offset is {:?}", picked_offset);
                println!("offset is {:?}", offset);
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[derive(Default)]
struct HostOpCircuit<F: FieldExt> {
    shared_operands: Vec<F>,
    shared_opcodes: Vec<F>,
    shared_index: Vec<F>,
}

/*
let base_chip = BaseChip::new(config.base_chip_config);
let range_chip = RangeChip::<N>::new(config.range_chip_config);
range_chip.init_table(&mut layouter)?;
*/


impl<F: FieldExt> Circuit<F> for HostOpCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostOpConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let shared_operands = meta.advice_column();
        let shared_opcodes = meta.advice_column();
        let shared_index = meta.advice_column();
        let filtered_operands = meta.advice_column();
        let filtered_opcodes = meta.advice_column();
        let filtered_index = meta.advice_column();

        HostOpChip::configure(
            meta,
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index,
            F::one(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let host_op_chip = HostOpChip::<F>::construct(config);
        host_op_chip.assign(
            &mut layouter,
            &self.shared_operands,
            &self.shared_opcodes,
            &self.shared_index,
            F::one()
        )?;
        Ok(())
    }
}

#[allow(clippy::many_single_char_names)]
fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr as Fp;

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 4;

    // Prepare the private and public inputs to the circuit!
    let a = Fp::one();
    let b = Fp::one();
    let c = a + b;
    let shared_operands = vec![Fp::zero(), a, b, c];
    let shared_opcodes = vec![Fp::zero(), Fp::one(), Fp::one(), Fp::one()];
    let shared_index = vec![Fp::zero(), Fp::one(), Fp::from(2), Fp::from(3)];

    // Instantiate the circuit with the private inputs.
    let circuit = HostOpCircuit {
        shared_operands,
        shared_opcodes,
        shared_index,
    };

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}
