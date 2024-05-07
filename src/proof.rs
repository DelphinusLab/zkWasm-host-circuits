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
    map_to_curve::Map2CurveChip,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    pairing::bn256::{Bn256, Fr},
    plonk::{Circuit, ConstraintSystem, Error},
};
use std::{fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use circuits_batcher::args::HashType::Poseidon;
use circuits_batcher::proof::CircuitInfo;
use circuits_batcher::proof::Prover;

use crate::host::ExternalHostCallEntryTable;
use serde::{Deserialize, Serialize};

pub const MERKLE_DEPTH: usize = 32;

trait HostCircuit<F: FieldExt>: Clone {
    fn load_shared_operands(&self, layouter: impl Layouter<F>, a: Vec<F>) -> Result<Self, Error>;
    fn filter(&self, layouter: impl Layouter<F>) -> Result<Self, Error>;
}

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
    MAP2CURVE,
}

#[derive(Clone)]
pub struct HostOpCircuit<F: FieldExt, S: HostOpSelector> {
    shared_operands: Vec<F>,
    shared_opcodes: Vec<F>,
    k: usize,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Default for HostOpCircuit<F, S> {
    fn default() -> Self {
        HostOpCircuit {
            shared_operands: Vec::<F>::default(),
            shared_opcodes: Vec::<F>::default(),
            k: 22,
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
    type FloorPlanner = SimpleFloorPlanner;

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

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let host_op_chip =
            HostOpChip::<Fr, S>::construct(config.hostconfig.clone(), config.selectconfig.clone());
        let mut selector_chip = S::construct(config.selectconfig);
        let all_arg_cells = layouter.assign_region(
            || "filter operands and opcodes",
            |mut region| {
                let mut offset = 0;
                let all_arg_cells = host_op_chip.assign(
                    &mut region,
                    self.k,
                    &mut offset,
                    &self.shared_operands,
                    &self.shared_opcodes,
                )?;

                println!("total arg cells: {:?}", all_arg_cells.len());
                println!("selector offset start at: {:?}", offset);
                selector_chip.synthesize(&mut offset, &all_arg_cells, &mut region)?;
                Ok(all_arg_cells)
            },
        )?;
        selector_chip.synthesize_separate(&all_arg_cells, &mut layouter)?;
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
) -> HostOpCircuit<Fr, S> {
    // Prepare the private and public inputs to the circuit!
    let shared_operands = v.0.iter().map(|x| Fr::from(x.value as u64)).collect();
    let shared_opcodes = v.0.iter().map(|x| Fr::from(x.op as u64)).collect();

    HostOpCircuit::<Fr, S> {
        shared_operands,
        shared_opcodes,
        k,
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
    use circuits_batcher::proof::K_PARAMS_CACHE;
    use circuits_batcher::proof::PKEY_CACHE;
    match opname {
        OpType::BLS381PAIR => {
            let bls381pair_circuit = build_host_circuit::<Bls381PairChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, Bls381PairChip<Fr>>> =
                CircuitInfo::new(
                    bls381pair_circuit,
                    format!("{}.{:?}", name, opname),
                    vec![],
                    k,
                    Poseidon,
                );
            //prover.mock_proof(k as u32);
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::BLS381SUM => {
            let bls381sum_circuit = build_host_circuit::<Bls381SumChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, Bls381SumChip<Fr>>> = CircuitInfo::new(
                bls381sum_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            //prover.mock_proof(k as u32);
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::BN256PAIR => {
            let bn256pair_circuit = build_host_circuit::<Bn256PairChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, Bn256PairChip<Fr>>> = CircuitInfo::new(
                bn256pair_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            //prover.mock_proof(k as u32);
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::BN256SUM => {
            let bn256sum_circuit = build_host_circuit::<Bn256SumChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, Bn256SumChip<Fr>>> = CircuitInfo::new(
                bn256sum_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            //prover.mock_proof(k as u32);
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::POSEIDONHASH => {
            let poseidon_circuit = build_host_circuit::<PoseidonChip<Fr, 9, 8>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, PoseidonChip<Fr, 9, 8>>> =
                CircuitInfo::new(
                    poseidon_circuit,
                    format!("{}.{:?}", name, opname),
                    vec![],
                    k,
                    Poseidon,
                );
            prover.mock_proof(k as u32);
            println!("mock proof for poseidon hash success");
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::MERKLE => {
            let merkle_circuit = build_host_circuit::<MerkleChip<Fr, MERKLE_DEPTH>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, MerkleChip<Fr, MERKLE_DEPTH>>> =
                CircuitInfo::new(
                    merkle_circuit,
                    format!("{}.{:?}", name, opname),
                    vec![],
                    k,
                    Poseidon,
                );
            prover.mock_proof(k as u32);
            println!("mock proof for merkle success");
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::JUBJUBSUM => {
            let jubjub_circuit = build_host_circuit::<AltJubChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, AltJubChip<Fr>>> = CircuitInfo::new(
                jubjub_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            prover.mock_proof(k as u32);
            println!("mock proof for jubjub success");
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::KECCAKHASH => {
            let keccak_circuit = build_host_circuit::<KeccakChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, KeccakChip<Fr>>> = CircuitInfo::new(
                keccak_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            prover.mock_proof(k as u32);
            println!("mock proof for keccak success");
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
        OpType::MAP2CURVE => {
            let map2curve_circuit = build_host_circuit::<Map2CurveChip<Fr>>(&v, k);
            let prover: CircuitInfo<Bn256, HostOpCircuit<Fr, Map2CurveChip<Fr>>> = CircuitInfo::new(
                map2curve_circuit,
                format!("{}.{:?}", name, opname),
                vec![],
                k,
                Poseidon,
            );
            prover.mock_proof(k as u32);
            println!("mock proof for map2curve success");
            prover.proofloadinfo.save(&cache_folder.as_path());
            prover.exec_create_proof(
                cache_folder.as_path(),
                param_folder.as_path(),
                PKEY_CACHE.lock().as_mut().unwrap(),
                0,
                K_PARAMS_CACHE.lock().as_mut().unwrap(),
            );
        }
    };
    println!("Proof generated.");
}
