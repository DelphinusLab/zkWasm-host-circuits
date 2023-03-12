mod utils;
mod circuits;
mod host;

use std::marker::PhantomData;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Fixed, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};
use clap::{arg, value_parser, App, Arg, ArgMatches};
use std::{
    io::BufReader,
    fs::File,
    path::PathBuf,
};

use crate::circuits::{
    HostOpSelector,
    bls::Bls381PairChip,
};

use halo2ecc_s::circuit::{
    base_chip::{BaseChip, BaseChipConfig},
    range_chip::{RangeChip, RangeChipConfig}
};

use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::dev::MockProver;

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

#[derive(clap::Parser)]
struct ArgOpName {
       #[clap(arg_enum)]
       t: OpType,
}
#[derive(clap::ArgEnum, Clone, Debug)]
enum OpType {
    BLS381PAIR,
    POSEDONHASH,
}

// ANCHOR: add-config
#[derive(Clone, Debug)]
struct HostOpConfig<S: Clone + std::fmt::Debug> {
    shared_operands: Column<Advice>,
    shared_opcodes: Column<Advice>,
    shared_index: Column<Advice>,
    filtered_operands: Column<Advice>,
    filtered_opcodes: Column<Advice>,
    filtered_index: Column<Advice>,
    merged_operands: Column<Advice>,
    indicator: Column<Fixed>,
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    selector_chip_config: S,
}

struct HostOpChip<F: FieldExt, S: HostOpSelector> {
    config: HostOpConfig<S::Config>,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Chip<F> for HostOpChip<F, S> {
    type Config = HostOpConfig<S::Config>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<S: HostOpSelector> HostOpChip<Fr, S> {
    fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_operands: Column<Advice>,
        shared_opcodes: Column<Advice>,
        shared_index: Column<Advice>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> <Self as Chip<Fr>>::Config {
        meta.lookup_any("filter-shared-ops", |meta| {
            let sopc = meta.query_advice(shared_opcodes, Rotation::cur());
            let soper = meta.query_advice(shared_operands, Rotation::cur());
            let sidx = meta.query_advice(shared_index, Rotation::cur());
            let foper = meta.query_advice(filtered_operands, Rotation::cur());
            let fopc  = meta.query_advice(filtered_opcodes, Rotation::cur());
            let fidx = meta.query_advice(filtered_index, Rotation::cur());
            vec![(fidx, sidx), (foper, soper), (fopc, sopc)]
        });

        meta.create_gate("merge operands in filtered columns", |meta| {
            let merged_op_res = meta.query_advice(merged_operands, Rotation::next());
            let cur_op = meta.query_advice(filtered_operands, Rotation::cur());
            let next_op = meta.query_advice(filtered_operands, Rotation::next());
            let indicator = meta.query_fixed(indicator, Rotation::cur());
            vec![indicator * (merged_op_res - (next_op * constant!(Fr::from(1u64 << 54)) + cur_op))]
        });

        meta.enable_equality(merged_operands);


        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<Fr>::configure(meta);
        let selector_chip_config = S::configure(meta, &base_chip_config, &range_chip_config);

        HostOpConfig {
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index,
            merged_operands,
            indicator,
            base_chip_config,
            range_chip_config,
            selector_chip_config,
        }
    }

    fn assign(
        &self,
        layouter: &mut impl Layouter<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        target_opcode: Fr,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error>  {
        let mut arg_cells = None ;
        layouter.assign_region(
            || "filter operands and opcodes",
            |mut region| {
                println!("asign_region");
                let mut offset = 0;
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
                    offset += 1;
                };
                arg_cells = Some (S::assign(
                    &mut region,
                    shared_operands,
                    shared_opcodes,
                    shared_index,
                    self.config.filtered_operands,
                    self.config.filtered_opcodes,
                    self.config.filtered_index,
                    self.config.merged_operands,
                    self.config.indicator,
                )?);
                println!("offset is {:?}", offset);
                Ok(())
            },
        )?;
        Ok(arg_cells.unwrap())
    }
}

struct HostOpCircuit<F: FieldExt, S: HostOpSelector> {
    shared_operands: Vec<F>,
    shared_opcodes: Vec<F>,
    shared_index: Vec<F>,
    _marker: PhantomData<(F, S)>,
}

impl<F:FieldExt, S: HostOpSelector> Default for HostOpCircuit<F, S> {
    fn default() -> Self {
        HostOpCircuit {
            shared_operands: Vec::<F>::default(),
            shared_opcodes: Vec::<F>::default(),
            shared_index: Vec::<F>::default(),
            _marker: PhantomData,

        }
    }
}

pub const BLS381FQ_SIZE: usize = 8;
pub const BLS381G1_SIZE: usize = 17;
pub const BLS381G2_SIZE: usize = 33;
pub const BLS381GT_SIZE: usize = 96;

impl<S: HostOpSelector> Circuit<Fr> for HostOpCircuit<Fr, S> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostOpConfig<S::Config>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let shared_operands = meta.advice_column();
        let shared_opcodes = meta.advice_column();
        let shared_index = meta.advice_column();
        let filtered_operands = meta.advice_column();
        let filtered_opcodes = meta.advice_column();
        let filtered_index = meta.advice_column();
        let merged_operands = meta.advice_column();
        let indicator_index = meta.fixed_column();

        HostOpChip::<Fr, S>::configure (
            meta,
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index,
            merged_operands,
            indicator_index,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let host_op_chip = HostOpChip::<Fr, S>::construct(config.clone());
        let mut all_arg_cells = host_op_chip.assign(
            &mut layouter,
            &self.shared_operands,
            &self.shared_opcodes,
            &self.shared_index,
            Fr::one()
        )?;
        all_arg_cells.retain(|x| x.value().is_some());
        let base_chip = BaseChip::new(config.base_chip_config);
        let range_chip = RangeChip::<Fr>::new(config.range_chip_config);
        range_chip.init_table(&mut layouter)?;
        println!("arg cell num is: {:?}", all_arg_cells.len());
        let selector_chip = S::construct(config.selector_chip_config);
        selector_chip.synthesize(&all_arg_cells, &base_chip, &range_chip, &mut layouter)?;
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

    let clap_app = App::new("playground")
        .arg(input_file())
        .arg(opname());

    let matches = clap_app.get_matches();
    let input_file = parse_input_file(&matches);
    let opname = parse_opname(&matches);

    let file = File::open(input_file).expect("File does not exist");
    let v: host::ExternalHostCallEntryTable = match serde_json::from_reader(BufReader::new(file)) {
        Err(e) => {
            println!("load json error {:?}", e);
            unreachable!();
        },
        Ok(o) => o
    };

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 22;

    // Prepare the private and public inputs to the circuit!
    let shared_operands = v.0.iter().map(|x| Fr::from(x.value as u64)).collect();
    let shared_opcodes = v.0.iter().map(|x| Fr::from(x.op as u64)).collect();
    let shared_index = v.0.iter()
        .enumerate()
        .map(|(i, _)| Fr::from(i as u64))
        .collect();

    // Instantiate the circuit with the private inputs.
    let circuit = match opname {
        OpType::BLS381PAIR => {
            HostOpCircuit::<Fr, Bls381PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData
            }
        },
        OpType::POSEDONHASH => {
            todo!()
        }
    };

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
    println!("Mock Verify Pass.");
}




