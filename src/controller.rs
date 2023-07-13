use actix_web::{ get, web, Responder, HttpResponse, HttpRequest };
use actix_web::body::EitherBody;
use halo2_proofs::pairing::bn256::Fr;
use std::{
    path::PathBuf,
    marker::PhantomData
};
use crate::host::ExternalHostCallEntryTable;
use crate::utils::params::{HostCircuitInfo, Prover};
use crate::{ HostOpCircuit, OpType };
use crate::circuits::{
    bls::Bls381PairChip, bls::Bls381SumChip,
    bn256::Bn256PairChip, bn256::Bn256SumChip,
    poseidon::PoseidonChip,
    merkle::MerkleChip,
};
use halo2_proofs::pairing::bn256::Bn256;
use serde::{ Deserialize, Serialize };

#[derive(Deserialize, Debug)]
pub struct QueryReq {
    pub host_call_entry_table: Option<ExternalHostCallEntryTable>,
    pub opname: Option<OpType>,
    pub output_folder: Option<PathBuf>,
}

impl QueryReq {
    pub fn default() -> Self {
        QueryReq {
            host_call_entry_table: None,
            opname: None,
            output_folder: None,
        }
    }
}

#[derive(Debug, Serialize, Clone)]
pub struct RequestResult<T: Serialize + Clone> {
    pub success: bool,
    pub result: T,
}

impl<T: Serialize + Clone> Responder for RequestResult<T> {
    type Body = EitherBody<String>;
    fn respond_to(self, req: &HttpRequest) -> HttpResponse<Self::Body> {
        web::Json(self).respond_to(req)
    }
}

#[get("/createproof")]
pub async fn createproof(_req_body: web::Query<QueryReq>) -> Result<RequestResult<Vec<u8>>, std::io::Error> {
    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 22;

    // Prepare the private and public inputs to the circuit!
    let shared_operands = _req_body.host_call_entry_table.as_ref().unwrap().0.iter().map(|x| Fr::from(x.value as u64)).collect();
    let shared_opcodes = _req_body.host_call_entry_table.as_ref().unwrap().0.iter().map(|x| Fr::from(x.op as u64)).collect();
    let shared_index =
        _req_body.host_call_entry_table.as_ref().unwrap().0.iter()
        .enumerate()
        .map(|(i, _)| Fr::from(i as u64))
        .collect();

    // Instantiate the circuit with the private inputs.
    // Given the correct public input, our circuit will verify.
    let result: Vec<u8> = match _req_body.opname.as_ref().unwrap() {
        OpType::BLS381PAIR => {
            let bls381pair_circuit = HostOpCircuit::<Fr, Bls381PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bls381PairChip<Fr>>> = HostCircuitInfo::new(bls381pair_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
        OpType::BLS381SUM => {
            let bls381sum_circuit = HostOpCircuit::<Fr, Bls381SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bls381SumChip<Fr>>> = HostCircuitInfo::new(bls381sum_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
        OpType::BN256PAIR => {
            let bn256pair_circuit = HostOpCircuit::<Fr, Bn256PairChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bn256PairChip<Fr>>> = HostCircuitInfo::new(bn256pair_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
        OpType::BN256SUM => {
            let bn256sum_circuit = HostOpCircuit::<Fr, Bn256SumChip<Fr>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, Bn256SumChip<Fr>>> = HostCircuitInfo::new(bn256sum_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
        OpType::POSEIDONHASH => {
            let poseidon_circuit = HostOpCircuit::<Fr, PoseidonChip<Fr, 9, 8>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, PoseidonChip<Fr, 9 ,8>>> = HostCircuitInfo::new(poseidon_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
        OpType::MERKLE => {
            let merkle_circuit = HostOpCircuit::<Fr, MerkleChip<Fr, 20>> {
                shared_operands,
                shared_opcodes,
                shared_index,
                _marker: PhantomData,
            };
            let prover: HostCircuitInfo<Bn256, HostOpCircuit<Fr, MerkleChip<Fr, 20>>> = HostCircuitInfo::new(merkle_circuit, format!("{:?}", _req_body.opname), vec![]);
            prover.mock_proof(k);
            prover.create_proof(_req_body.output_folder.as_ref().unwrap().as_path(), k)
        }
    };

    Ok(RequestResult {
        success: true,
        result: result
    })
}
