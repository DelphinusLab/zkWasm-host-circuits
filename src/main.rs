//#![deny(warnings)]
mod adaptor;
pub mod circuits;
pub mod host;
pub mod proof;
pub mod utils;

use crate::proof::{exec_create_host_proof, read_host_call_table, OpType};
use clap::{arg, value_parser, App, Arg, ArgMatches};
use std::path::PathBuf;

const DEFAULT_CIRCUITS_K: u32 = 22;

#[derive(clap::Parser)]
struct ArgOpName {
    #[clap(arg_enum)]
    t: OpType,
}

fn circuits_k<'a>() -> Arg<'a> {
    arg!(-k --K<CIRCUITS_SIZE> "Circuit size K")
        .required(false)
        .value_parser(value_parser!(u32))
}

fn parse_circuits_k(matches: &ArgMatches) -> u32 {
    matches
        .get_one::<u32>("K")
        .unwrap_or(&DEFAULT_CIRCUITS_K)
        .clone()
}

fn output_folder<'a>() -> Arg<'a> {
    arg!(-o --output<OUTPUT_FOLDER>... "output file folder that contains all proof results")
        .max_values(1)
        .value_parser(value_parser!(PathBuf))
}

fn parse_output_folder(matches: &ArgMatches) -> PathBuf {
    matches
        .get_one::<PathBuf>("output")
        .expect("output folder is required")
        .clone()
}

fn param_folder<'a>() -> Arg<'a> {
    arg!(-p --param<PARAM_FOLDER>... "param file folder that contains all setup results")
        .max_values(1)
        .value_parser(value_parser!(PathBuf))
}

fn parse_param_folder(matches: &ArgMatches) -> PathBuf {
    matches
        .get_one::<PathBuf>("param")
        .expect("param folder is required")
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
        .arg(param_folder())
        .arg(opname())
        .arg(circuits_k());

    let matches = clap_app.get_matches();
    let input_file = parse_input_file(&matches);
    let cache_folder = parse_output_folder(&matches);
    let param_folder = parse_param_folder(&matches);
    let opname = parse_opname(&matches);
    let k = parse_circuits_k(&matches);

    exec_create_host_proof(
        "host",
        k as usize,
        &read_host_call_table(input_file),
        opname,
        &cache_folder,
        &param_folder,
    );
}
