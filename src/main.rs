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


// ANCHOR: add-config
#[derive(Clone, Debug)]
struct HostSumConfig {
    advice: [Column<Advice>; 2],
    shared_operands: Column<Advice>,
    shared_opcodes: Column<Advice>,
    s_add: Selector,
}

struct HostSumChip<F: FieldExt> {
    config: HostSumConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for HostSumChip<F> {
    type Config = HostSumConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> HostSumChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        shared_operands: Column<Advice>,
        shared_opcodes: Column<Advice>,
    ) -> <Self as Chip<F>>::Config {
        let s_add = meta.selector();
        meta.create_gate("host-sum", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_add = meta.query_selector(s_add);
            vec![s_add]
        });

        HostSumConfig {
            advice,
            shared_operands,
            shared_opcodes,
            s_add,
        }
    }
}

#[derive(Default)]
struct HostSumCircuit<F: FieldExt> {
    shared_operands: Vec<F>,
}

impl<F: FieldExt> Circuit<F> for HostSumCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostSumConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let advice = [meta.advice_column(), meta.advice_column()];
        let shared_operands = meta.advice_column();
        let shared_opcodes = meta.advice_column();

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        HostSumChip::configure(meta, advice, shared_operands, shared_opcodes)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let host_sum_chip = HostSumChip::<F>::construct(config);
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


