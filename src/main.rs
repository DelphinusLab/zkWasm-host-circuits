mod utils;
mod circuits;

use std::marker::PhantomData;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
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
        filtered_index: Column<Advice>,
        opcode: F,
    ) -> <Self as Chip<F>>::Config {
        meta.lookup_any("filter-shared-ops", |meta| {
            let sopc = meta.query_advice(shared_opcodes, Rotation::cur());
            let soper = meta.query_advice(shared_operands, Rotation::cur());
            let sidx = meta.query_advice(shared_index, Rotation::cur());
            let foper = meta.query_advice(filtered_operands, Rotation::cur());
            let fidx = meta.query_advice(filtered_index, Rotation::cur());
            vec![(constant!(opcode), sopc), (foper, soper), (fidx, sidx)]
        });

        HostOpConfig {
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_index
        }
    }
}

#[derive(Default)]
struct HostSumCircuit<F: FieldExt> {
    shared_operands: Vec<F>,
}

impl<F: FieldExt> Circuit<F> for HostSumCircuit<F> {
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
        let filtered_index = meta.advice_column();

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        HostOpChip::configure(
            meta,
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_index,
            F::one(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let host_sum_chip = HostOpChip::<F>::construct(config);
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
    let shared_operands = vec![a, b, c];

    // Instantiate the circuit with the private inputs.
    let circuit = HostSumCircuit {
        shared_operands
    };

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // If we try some other public input, the proof will fail!
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert!(prover.verify().is_err());
    // ANCHOR_END: test-circuit
}


