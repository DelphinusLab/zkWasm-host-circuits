use crate::circuits::babyjub::AltJubChip;
use crate::circuits::{
    bls::Bls381PairChip,
    bls::Bls381SumChip,
    bn256::Bn256PairChip,
    bn256::Bn256SumChip,
    host::{HostOpChip, HostOpConfig, HostOpSelector},
    keccak256::KeccakChip,
    merkle::MerkleChip,
    poseidon::PoseidonChip,
};
use halo2_proofs::circuit::floor_planner::FlatFloorPlanner;
use halo2_proofs::pairing::bn256::Bn256;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Layouter,
    pairing::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::{fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use circuits_batcher::args::HashType::Poseidon;
use circuits_batcher::args::OpenSchema;
use circuits_batcher::proof::{ParamsCache, ProofGenerationInfo, ProofPieceInfo, ProvingKeyCache};

use crate::host::ExternalHostCallEntryTable;
use serde::{Deserialize, Serialize};

pub const MERKLE_DEPTH: usize = 32;

#[derive(clap::Parser)]
struct ArgOpName {
    #[clap(arg_enum)]
    t: OpType,
}
#[derive(clap::ArgEnum, Clone, Debug, Serialize, Deserialize)]
pub enum OpType {
    BLS381PAIR,
    BLS381SUM,
    BN256PAIR,
    BN256SUM,
    POSEIDONHASH,
    KECCAKHASH,
    MERKLE,
    JUBJUBSUM,
}

#[derive(Clone)]
pub struct HostOpCircuit<F: FieldExt, S: HostOpSelector> {
    shared_operands: Vec<F>,
    shared_opcodes: Vec<F>,
    helper: S::Helper,
    k: usize,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Default for HostOpCircuit<F, S> {
    fn default() -> Self {
        HostOpCircuit {
            shared_operands: Vec::<F>::default(),
            shared_opcodes: Vec::<F>::default(),
            k: 22,
            helper: S::Helper::default(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct HostCircuitConfig<C: Clone> {
    hostconfig: HostOpConfig,
    selectconfig: C,
}

impl<S: HostOpSelector> Circuit<Fr> for HostOpCircuit<Fr, S> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = HostCircuitConfig<S::Config>;
    type FloorPlanner = FlatFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let shared_advices = vec![
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        // We create the two advice columns that FieldChip uses for I/O.
        HostCircuitConfig {
            hostconfig: HostOpChip::<Fr, S>::configure(meta, &shared_advices),
            selectconfig: S::configure(meta, &shared_advices),
        }
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<Fr>) -> Result<(), Error> {
        let host_op_chip =
            HostOpChip::<Fr, S>::construct(config.hostconfig.clone(), config.selectconfig.clone());
        let (all_arg_cells, mut selector_chip) = layouter.assign_region(
            || "filter operands and opcodes",
            |region| {
                let mut offset = 0;
                let all_arg_cells = host_op_chip.assign(
                    &region,
                    self.k,
                    &mut offset,
                    &self.shared_operands,
                    &self.shared_opcodes,
                )?;
                let mut selector_chip = S::construct(config.selectconfig.clone());

                println!("total arg cells: {:?}", all_arg_cells.len());
                println!("selector offset start at: {:?}", offset);
                selector_chip.synthesize(&mut offset, &all_arg_cells, &region, &self.helper)?;
                Ok((all_arg_cells, selector_chip))
            },
        )?;
        selector_chip.synthesize_separate(&all_arg_cells, &layouter)?;
        Ok(())
    }
}

pub fn read_host_call_table(input_file: PathBuf) -> ExternalHostCallEntryTable {
    let file = File::open(input_file).expect("File does not exist");
    let v: ExternalHostCallEntryTable = match serde_json::from_reader(BufReader::new(file)) {
        Err(e) => {
            println!("load json error {:?}", e);
            unreachable!();
        }
        Ok(o) => o,
    };
    v
}

pub fn build_host_circuit<S: HostOpSelector>(
    v: &ExternalHostCallEntryTable,
    k: usize,
    helper: S::Helper,
) -> HostOpCircuit<Fr, S> {
    // Prepare the private and public inputs to the circuit!
    let shared_operands = v.0.iter().map(|x| Fr::from(x.value as u64)).collect();
    let shared_opcodes = v.0.iter().map(|x| Fr::from(x.op as u64)).collect();

    HostOpCircuit::<Fr, S> {
        shared_operands,
        shared_opcodes,
        k,
        helper,
        _marker: PhantomData,
    }
}

pub fn exec_create_host_proof(
    name: &str,
    k: usize,
    v: &ExternalHostCallEntryTable,
    opname: OpType,
    cache_folder: &PathBuf,
    param_folder: &PathBuf,
) {
    // Instantiate the circuit with the private inputs.
    // Given the correct public input, our circuit will verify.

    let mut params_cache = ParamsCache::<Bn256>::new(5, param_folder.clone());
    let mut pkey_cache = ProvingKeyCache::new(5, param_folder.clone());
    macro_rules! gen_proof {
        ($circuit: expr) => {
            let prover: ProofPieceInfo =
                ProofPieceInfo::new(format!("{}.{:?}", name, opname), 0, 0);
            let mut proof_gen_info =
                ProofGenerationInfo::new(format!("{}.{:?}", name, opname).as_str(), k, Poseidon);
            let proof = prover.exec_create_proof(
                &$circuit,
                &vec![],
                k,
                &mut pkey_cache,
                &mut params_cache,
                Poseidon,
                OpenSchema::GWC,
            );
            prover.save_proof_data::<Fr>(&vec![], &proof, cache_folder);
            //prover.mock_proof(k as u32);
            proof_gen_info.append_single_proof(prover);
            proof_gen_info.save(cache_folder);
        };
    }

    match opname {
        OpType::BLS381PAIR => {
            let circuit = build_host_circuit::<Bls381PairChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::BLS381SUM => {
            let circuit = build_host_circuit::<Bls381SumChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::BN256PAIR => {
            let circuit = build_host_circuit::<Bn256PairChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::BN256SUM => {
            let circuit = build_host_circuit::<Bn256SumChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::POSEIDONHASH => {
            let circuit = build_host_circuit::<PoseidonChip<Fr, 9, 8>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::MERKLE => {
            let circuit = build_host_circuit::<MerkleChip<Fr, MERKLE_DEPTH>>(&v, k, None);
            gen_proof!(circuit);
        }
        OpType::JUBJUBSUM => {
            let circuit = build_host_circuit::<AltJubChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
        OpType::KECCAKHASH => {
            let circuit = build_host_circuit::<KeccakChip<Fr>>(&v, k, ());
            gen_proof!(circuit);
        }
    };

    println!("Proof generated.");
}
