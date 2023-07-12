#![feature(array_zip)]
#![feature(slice_flatten)]
#![deny(warnings)]
pub mod circuits;
pub mod host;
pub mod utils;
mod adaptor;

/*
use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
    constant_from,
};
*/

use clap::{arg, value_parser, App, Arg, ArgMatches};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};



use std::{
    marker::PhantomData,
    fs::File,
    io::BufReader,
    path::PathBuf
};

use crate::circuits::{
    bls::Bls381PairChip, bls::Bls381SumChip,
    bn256::Bn256PairChip, bn256::Bn256SumChip,
    poseidon::PoseidonChip,
    merkle::MerkleChip,
    host::{
        HostOpSelector,
        HostOpChip,
        HostOpConfig,
    }
};

use crate::utils::params::{HostCircuitInfo, Prover};

use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::pairing::bn256::Bn256;

trait HostCircuit<F: FieldExt>: Clone {
    fn load_shared_operands(&self, layouter: impl Layouter<F>, a: Vec<F>) -> Result<Self, Error>;
    fn filter(&self, layouter: impl Layouter<F>) -> Result<Self, Error>;
}

#[derive(clap::Parser)]
struct ArgOpName {
    #[clap(arg_enum)]
    t: OpType,
}
#[derive(clap::ArgEnum, Clone, Debug)]
enum OpType {
    BLS381PAIR,
    BLS381SUM,
    BN256PAIR,
    BN256SUM,
    POSEIDONHASH,
    MERKLE,
}


#[derive(Clone)]
struct HostOpCircuit<F: FieldExt, S: HostOpSelector> {
    shared_operands: Vec<F>,
    shared_opcodes: Vec<F>,
    shared_index: Vec<F>,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Default for HostOpCircuit<F, S> {
    fn default() -> Self {
        HostOpCircuit {
            shared_operands: Vec::<F>::default(),
            shared_opcodes: Vec::<F>::default(),
            shared_index: Vec::<F>::default(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
struct HostCircuitConfig<C: Clone> {
    hostconfig: HostOpConfig,
    selectconfig: C,
}


impl<S: HostOpSelector> Circuit<Fr> for HostOpCircuit<Fr, S> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostCircuitConfig<S::Config>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        HostCircuitConfig {
            hostconfig: HostOpChip::<Fr, S>::configure(meta),
            selectconfig: S::configure(meta),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let host_op_chip = HostOpChip::<Fr, S>::construct(config.hostconfig.clone(), config.selectconfig.clone());
        let all_arg_cells = host_op_chip.assign(
            &mut layouter,
            &self.shared_operands,
            &self.shared_opcodes,
            &self.shared_index,
        )?;
        //all_arg_cells.retain(|x| x.value().is_some());
        let mut selector_chip = S::construct(config.selectconfig);
        println!("arg cell num is: {:?}", all_arg_cells.len());
        selector_chip.synthesize(&all_arg_cells, &mut layouter)?;
        Ok(())
    }
}

fn output_folder<'a>() -> Arg<'a> {
    arg!(-o --output<OUTPUT_FOLDER>... "output file folder that contains all setup and proof results")
        .max_values(1)
        .value_parser(value_parser!(PathBuf))
}

fn parse_output_folder(matches: &ArgMatches) -> PathBuf {
    matches
        .get_one::<PathBuf>("output")
        .expect("input file is required")
        .clone()
}

fn input_file<'a>() -> Arg<'a> {
    arg!(-i --input<INPUT_FILES>... "Input file that contains all host function call")
        .max_values(1)
        .value_parser(value_parser!(PathBuf))
}

fn parse_input_file(matches: &ArgMatches) -> PathBuf {
    matches
        .get_one::<PathBuf>("input")
        .expect("input file is required")
        .clone()
}

fn opname<'a>() -> Arg<'a> {
    arg!(-n --opname<OP_NAME>... "Operation name")
        .max_values(1)
        .value_parser(value_parser!(OpType))
}

fn parse_opname(matches: &ArgMatches) -> OpType {
    matches
        .get_one::<OpType>("opname")
        .expect("opname is required")
        .clone()
}

#[allow(clippy::many_single_char_names)]
fn main() {
    let clap_app = App::new("hostcircuit")
        .arg(input_file())
        .arg(output_folder())
        .arg(opname());

    let matches = clap_app.get_matches();
    let input_file = parse_input_file(&matches);
    let cache_folder = parse_output_folder(&matches);
    let opname = parse_opname(&matches);

    let file = File::open(input_file).expect("File does not exist");
    let v: host::ExternalHostCallEntryTable = match serde_json::from_reader(BufReader::new(file)) {
        Err(e) => {
            println!("load json error {:?}", e);
            unreachable!();
        }
        Ok(o) => o,
    };

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 22;

    // Prepare the private and public inputs to the circuit!
    let shared_operands = v.0.iter().map(|x| Fr::from(x.value as u64)).collect();
    let shared_opcodes = v.0.iter().map(|x| Fr::from(x.op as u64)).collect();
    let shared_index =
        v.0.iter()
            .enumerate()
            .map(|(i, _)| Fr::from(i as u64))
            .collect();

    // Instantiate the circuit with the private inputs.
    // Given the correct public input, our circuit will verify.
    match opname {
        OpType::BLS381PAIR => {
            let bls381pair_circuit = HostOpCircuit::<Fr, Bls381PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bls381PairChip<Fr>>> = HostCircuitInfo::new(bls381pair_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }
        OpType::BLS381SUM => {
            let bls381sum_circuit = HostOpCircuit::<Fr, Bls381SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bls381SumChip<Fr>>> = HostCircuitInfo::new(bls381sum_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }
        OpType::BN256PAIR => {
            let bn256pair_circuit = HostOpCircuit::<Fr, Bn256PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bn256PairChip<Fr>>> = HostCircuitInfo::new(bn256pair_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }
        OpType::BN256SUM => {
            let bn256sum_circuit = HostOpCircuit::<Fr, Bn256SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bn256SumChip<Fr>>> = HostCircuitInfo::new(bn256sum_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }
        OpType::POSEIDONHASH => {
            let poseidon_circuit = HostOpCircuit::<Fr, PoseidonChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, PoseidonChip<Fr>>> = HostCircuitInfo::new(poseidon_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }
        OpType::MERKLE => {
            let merkle_circuit = HostOpCircuit::<Fr, MerkleChip<Fr, 20>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, MerkleChip<Fr, 20>>> = HostCircuitInfo::new(merkle_circuit, format!("{:?}", opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(cache_folder.as_path(), k);
        }

    };

    //circuit_info.mock_proof(k);
    println!("Mock Verify Pass.");
}
