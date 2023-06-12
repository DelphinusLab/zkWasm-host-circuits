#![feature(array_zip)]
#![feature(slice_flatten)]
#![feature(int_log)]
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
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Region},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector, Expression, VirtualCells},
    poly::Rotation,
};



use std::{
    marker::PhantomData,
    fs::File,
    io::BufReader,
    path::PathBuf
};

use crate::circuits::{
    bls::Bls381PairChip, bls::Bls381SumChip, bn256::Bn256PairChip, bn256::Bn256SumChip,
    HostOpSelector,
};

use crate::utils::GateCell;
use crate::utils::params::{HostCircuitInfo, Prover};

customized_circuits!(HostOpConfig, 2, 7, 1, 0,
   | shared_operand | shared_opcode | shared_index | filtered_operand   | filtered_opcode  | filtered_index | merged_op   | indicator
   | nil            | nil           | nil          | filtered_operand_n | nil              | nil            | merged_op_n | nil
);

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
    POSEDONHASH,
}

struct HostOpChip<F: FieldExt, S: HostOpSelector> {
    config: HostOpConfig,
    selector_chip_config: S::Config,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Chip<F> for HostOpChip<F, S> {
    type Config = HostOpConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<S: HostOpSelector> HostOpChip<Fr, S> {
    fn construct(config: <Self as Chip<Fr>>::Config, selector_chip_config: S::Config) -> Self {
        Self {
            config,
            selector_chip_config,
            _marker: PhantomData,
        }
    }

    fn configure(
        cs: &mut ConstraintSystem<Fr>,
    ) -> <Self as Chip<Fr>>::Config {
        let witness= [0; 7]
                .map(|_| cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [cs.fixed_column()];
        let selector =[];

        let config = HostOpConfig { fixed, selector, witness };


        cs.lookup_any("filter-shared-ops", |meta| {
            let sopc = config.get_expr(meta, HostOpConfig::shared_opcode());
            let soper = config.get_expr(meta, HostOpConfig::shared_operand());
            let sidx = config.get_expr(meta, HostOpConfig::shared_index());
            let fopc= config.get_expr(meta, HostOpConfig::filtered_opcode());
            let foper = config.get_expr(meta, HostOpConfig::filtered_operand());
            let fidx = config.get_expr(meta, HostOpConfig::filtered_index());
            vec![(fidx, sidx), (foper, soper), (fopc, sopc)]
        });

        cs.create_gate("merge operands in filtered columns", |meta| {
            let merged_op_n = config.get_expr(meta, HostOpConfig::merged_op_n());
            let cur_op = config.get_expr(meta, HostOpConfig::filtered_operand());
            let next_op = config.get_expr(meta, HostOpConfig::filtered_operand_n());
            let indicator = config.get_expr(meta, HostOpConfig::indicator());
            vec![indicator.clone() * (merged_op_n - (next_op * indicator + cur_op))]
        });

        config
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let mut arg_cells = None;
        layouter.assign_region(
            || "filter operands and opcodes",
            |mut region| {
                println!("asign_region");
                let mut offset = 0;
                for opcode in shared_opcodes {
                    println!("opcode is {:?}", opcode);
                    self.config.assign_cell(
                        &mut region,
                        offset,
                        &HostOpConfig::shared_opcode(),
                        opcode.clone()
                    )?;
                    self.config.assign_cell(
                        &mut region,
                        offset,
                        &HostOpConfig::shared_operand(),
                        shared_operands[offset],
                    )?;
                    self.config.assign_cell(
                        &mut region,
                        offset,
                        &HostOpConfig::shared_index(),
                        shared_index[offset],
                    )?;
                    offset += 1;
                }
                arg_cells = Some(S::assign(
                    &mut region,
                    shared_operands,
                    shared_opcodes,
                    shared_index,
                    self.config.get_advice_column(HostOpConfig::filtered_operand()),
                    self.config.get_advice_column(HostOpConfig::filtered_opcode()),
                    self.config.get_advice_column(HostOpConfig::filtered_index()),
                    self.config.get_advice_column(HostOpConfig::merged_op()),
                    self.config.get_fixed_column(HostOpConfig::indicator()),
                )?);
                println!("offset is {:?}", offset);
                Ok(())
            },
        )?;
        Ok(arg_cells.unwrap())
    }
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
        let mut all_arg_cells = host_op_chip.assign(
            &mut layouter,
            &self.shared_operands,
            &self.shared_opcodes,
            &self.shared_index,
        )?;
        all_arg_cells.retain(|x| x.value().is_some());
        let selector_chip = S::construct(config.selectconfig);
        println!("arg cell num is: {:?}", all_arg_cells.len());
        selector_chip.synthesize(&all_arg_cells, &mut layouter)?;
        Ok(())
    }
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
    arg!(-o --opname<OP_NAME>... "Operation name")
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
    let clap_app = App::new("hostcircuit").arg(input_file()).arg(opname());

    let matches = clap_app.get_matches();
    let input_file = parse_input_file(&matches);
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
    let circuit_info: Box<dyn Prover::<Bn256>> = match opname {
        OpType::BLS381PAIR => {
            let bls381pair_circuit = HostOpCircuit::<Fr, Bls381PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            Box::new(HostCircuitInfo::new(bls381pair_circuit, format!("{:?}", opname), vec![vec![]]))
        }
        OpType::BLS381SUM => {
            let bls381sum_circuit = HostOpCircuit::<Fr, Bls381SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            Box::new(HostCircuitInfo::new(bls381sum_circuit, format!("{:?}", opname), vec![vec![]]))
        }
        OpType::BN256PAIR => {
            let bn256pair_circuit = HostOpCircuit::<Fr, Bn256PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            Box::new(HostCircuitInfo::new(bn256pair_circuit, "opname.into()".to_string(), vec![vec![]]))
        }
        OpType::BN256SUM => {
            let bn256sum_circuit = HostOpCircuit::<Fr, Bn256SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            Box::new(HostCircuitInfo::new(bn256sum_circuit, "opname.into()".to_string(), vec![vec![]]))
        }
        OpType::POSEDONHASH => {
            todo!()
        }
    };

    circuit_info.mock_proof(k);
    println!("Mock Verify Pass.");
}
