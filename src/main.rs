mod utils;
mod circuits;
mod host;

use std::{marker::PhantomData, ops::Shl};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
    pairing::bls12_381::{G1Affine, G2Affine, G1, G2}
};
use clap::{arg, value_parser, App, Arg, ArgMatches};
use halo2_proofs::dev::MockProver;
use std::{
    io::BufReader,
    fs::File,
    path::PathBuf,
};

use crate::circuits::bls::{
    Bls381ChipConfig,
    Bls381PairChip,
};

use crate::utils::field_to_bn;

use halo2ecc_s::circuit::{
    base_chip::{BaseChip, BaseChipConfig},
    range_chip::{RangeChip, RangeChipConfig}
};

use halo2_proofs::pairing::bn256::Fr;
use num_bigint::BigUint;

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

use halo2_proofs::pairing::bls12_381::{
    Fq as Bls381Fq,
    Gt as Bls381Gt,
};

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
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    bls381_chip_config: Bls381ChipConfig,
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

impl HostOpChip<Fr> {
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
        opcode: Fr,
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

        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<Fr>::configure(meta);
        let bls381_chip_config = Bls381PairChip::<Fr>::configure(
            meta,
            base_chip_config.clone(),
            range_chip_config.clone()
        );

        HostOpConfig {
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index,
            base_chip_config,
            range_chip_config,
            bls381_chip_config,
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
        let mut arg_cells = vec![];
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
                        let opcell = region.assign_advice(
                            || "picked operands",
                            self.config.filtered_operands,
                            picked_offset,
                            || Ok(shared_operands[offset])
                        )?;
                        arg_cells.append(&mut vec![opcell]);
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
        Ok(arg_cells)
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


impl Circuit<Fr> for HostOpCircuit<Fr> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostOpConfig;
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

        HostOpChip::configure(
            meta,
            shared_operands,
            shared_opcodes,
            shared_index,
            filtered_operands,
            filtered_opcodes,
            filtered_index,
            Fr::one(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let host_op_chip = HostOpChip::<Fr>::construct(config.clone());
        let mut all_arg_cells = host_op_chip.assign(
            &mut layouter,
            &self.shared_operands,
            &self.shared_opcodes,
            &self.shared_index,
            Fr::one()
        )?;
        all_arg_cells.retain(|x| x.value().is_some());
        let a = all_arg_cells[0..19].to_vec();
        let b = all_arg_cells[19..56].to_vec();
        let ab = all_arg_cells[56..164].to_vec();
        let base_chip = BaseChip::new(config.base_chip_config);
        let range_chip = RangeChip::<Fr>::new(config.range_chip_config);
        let bls381_chip = Bls381PairChip::construct(config.bls381_chip_config.clone());
        bls381_chip.load_bls381_pair_circuit(&a, &b, &ab, &base_chip, &range_chip, layouter)?;
        Ok(())
    }
}

use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct ExternalHostCallEntry {
    pub op: usize,
    pub value: u64,
    pub is_ret: bool,
}

#[derive(Serialize, Deserialize, Debug)]
struct ExternalHostCallEntryTable(Vec<ExternalHostCallEntry>);

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

#[allow(clippy::many_single_char_names)]
fn main() {

    let clap_app = App::new("playground")
        .arg(input_file());

    let matches = clap_app.get_matches();
    let input_file = parse_input_file(&matches);

    let file = File::open(input_file).expect("File does not exist");
    let v: ExternalHostCallEntryTable = match serde_json::from_reader(BufReader::new(file)) {
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
    let circuit = HostOpCircuit {
        shared_operands,
        shared_opcodes,
        shared_index,
    };

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}

fn bls381_fr_to_pair_args(f: Bls381Fq, is_ret: bool) -> Vec<ExternalHostCallEntry> {
    let mut bn = field_to_bn(&f);
    let mut ret = vec![];
    for _ in 0..9 {
        let d:BigUint = BigUint::from(2 as u64).shl(45);
        let r = bn.clone() % d.clone();
        let value = if r == BigUint::from(0 as u32) {
            0 as u64
        } else {
            r.to_u64_digits()[0]
        };
        println!("d is {:?}, remainder is {:?}", d, r);
        bn = bn / d;
        let entry = ExternalHostCallEntry {
            op: 1,
            value,
            is_ret,
        };
        ret.append(&mut vec![entry]);
    };
    ret
}

fn bls381_gt_to_pair_args(f: Bls381Gt) -> Vec<ExternalHostCallEntry> {
    let c000 = bls381_fr_to_pair_args(f.0.c0.c0.c0, true);
    let c001 = bls381_fr_to_pair_args(f.0.c0.c0.c1, true);
    let c010 = bls381_fr_to_pair_args(f.0.c0.c1.c0, true);
    let c011 = bls381_fr_to_pair_args(f.0.c0.c1.c1, true);
    let c020 = bls381_fr_to_pair_args(f.0.c0.c2.c0, true);
    let c021 = bls381_fr_to_pair_args(f.0.c0.c2.c1, true);
    let c100 = bls381_fr_to_pair_args(f.0.c1.c0.c0, true);
    let c101 = bls381_fr_to_pair_args(f.0.c1.c0.c1, true);
    let c110 = bls381_fr_to_pair_args(f.0.c1.c1.c0, true);
    let c111 = bls381_fr_to_pair_args(f.0.c1.c1.c1, true);
    let c120 = bls381_fr_to_pair_args(f.0.c1.c2.c0, true);
    let c121 = bls381_fr_to_pair_args(f.0.c1.c2.c1, true);
    vec![c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121].into_iter().flatten().collect()
}

fn bls381_g1_to_pair_args(g:G1Affine) -> Vec<ExternalHostCallEntry> {
    let mut a = bls381_fr_to_pair_args(g.x, false);
    let mut b = bls381_fr_to_pair_args(g.y, false);
    let z:u64 = g.is_identity().unwrap_u8() as u64;
    a.append(&mut b);
    a.append(&mut vec![ExternalHostCallEntry{
        op:1,
        value: z,
        is_ret:false,
    }]);
    a
}

fn bls381_g2_to_pair_args(g:G2Affine) -> Vec<ExternalHostCallEntry> {
    let x0 = bls381_fr_to_pair_args(g.x.c0, false);
    let x1 = bls381_fr_to_pair_args(g.x.c1, false);
    let y0 = bls381_fr_to_pair_args(g.y.c0, false);
    let y1 = bls381_fr_to_pair_args(g.y.c1, false);
    let z:u64 = g.is_identity().unwrap_u8() as u64;
    let zentry = ExternalHostCallEntry{
        op:1,
        value: z,
        is_ret:false,
    };
    vec![x0,x1,y0,y1, vec![zentry]].into_iter().flatten().collect()
}


#[cfg(test)]
mod tests {
    use rand::rngs::OsRng;
    use halo2_proofs::pairing::bls12_381::pairing;
    use halo2_proofs::pairing::bls12_381::{G1Affine, G2Affine, G1, G2, Gt as Bls381Gt};
    use halo2_proofs::pairing::group::Group;
    use crate::{
        ExternalHostCallEntryTable,
        bls381_g1_to_pair_args,
        bls381_g2_to_pair_args,
        bls381_gt_to_pair_args,
    };
    use std::fs::File;

    #[test]
    fn generate_bls_input() {
        let a:G1Affine = G1::random(&mut OsRng).into();
        let b:G2Affine = G2Affine::from(G2::random(&mut OsRng));
        let ab:Bls381Gt = pairing(&a, &b);
        let g1_args = bls381_g1_to_pair_args(a);
        let g2_args = bls381_g2_to_pair_args(b);
        let ab_args = bls381_gt_to_pair_args(ab);
        let table = ExternalHostCallEntryTable (
            vec![g1_args, g2_args, ab_args].into_iter().flatten().collect()
        );
        let file = File::create("blstest.json").expect("can not create file");
        serde_json::to_writer(file, &table).expect("can not write to file");
        /* todo: output to blstest.json */
    }
}
