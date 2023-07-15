use ark_std::rand::rngs::OsRng;
use halo2_proofs::arithmetic::MultiMillerLoop;
use halo2_proofs::dev::MockProver;
use halo2_proofs::plonk::create_proof;
use halo2_proofs::plonk::keygen_pk;
use halo2_proofs::plonk::keygen_vk;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::VerifyingKey;
use halo2_proofs::poly::commitment::Params;
use halo2aggregator_s::transcript::poseidon::PoseidonWrite;
use std::io::Write;
use std::path::Path;

/*
use std::io::Read;
use halo2_proofs::poly::commitment::ParamsVerifier;
use halo2_proofs::plonk::verify_proof;
use halo2_proofs::plonk::SingleVerifier;
*/

pub fn load_or_build_unsafe_params<E: MultiMillerLoop>(
    k: u32,
    cache_file_opt: Option<&Path>,
) -> Params<E::G1Affine> {
    if let Some(cache_file) = &cache_file_opt {
        if Path::exists(&cache_file) {
            println!("read params K={} from {:?}", k, cache_file);
            let mut fd = std::fs::File::open(&cache_file).unwrap();
            return Params::<E::G1Affine>::read(&mut fd).unwrap();
        }
    }

    let params = Params::<E::G1Affine>::unsafe_setup::<E>(k);

    if let Some(cache_file) = &cache_file_opt {
        println!("write params K={} to {:?}", k, cache_file);
        let mut fd = std::fs::File::create(&cache_file).unwrap();
        params.write(&mut fd).unwrap();
    };

    params
}

pub fn load_vkey<E: MultiMillerLoop, C: Circuit<E::Scalar>>(
    params: &Params<E::G1Affine>,
    cache_file: &Path,
) -> VerifyingKey<E::G1Affine> {
    println!("read vkey from {:?}", cache_file);
    let mut fd = std::fs::File::open(&cache_file).unwrap();
    VerifyingKey::read::<_, C>(&mut fd, params).unwrap()
}

pub fn load_or_build_vkey<E: MultiMillerLoop, C: Circuit<E::Scalar>>(
    params: &Params<E::G1Affine>,
    circuit: &C,
    cache_file_opt: Option<&Path>,
) -> VerifyingKey<E::G1Affine> {
    if let Some(cache_file) = &cache_file_opt {
        if Path::exists(&cache_file) {
            return load_vkey::<E, C>(params, &cache_file);
        }
    }

    let verify_circuit_vk = keygen_vk(&params, circuit).expect("keygen_vk should not fail");

    if let Some(cache_file) = &cache_file_opt {
        println!("write vkey to {:?}", cache_file);
        let mut fd = std::fs::File::create(&cache_file).unwrap();
        verify_circuit_vk.write(&mut fd).unwrap();
    };

    verify_circuit_vk
}

pub struct HostCircuitInfo<E: MultiMillerLoop, C: Circuit<E::Scalar>> {
    pub circuit: C,
    pub name: String,
    pub instances: Vec<Vec<E::Scalar>>,
}

impl<E: MultiMillerLoop, C: Circuit<E::Scalar>> HostCircuitInfo<E, C> {
    pub fn new(c: C, name: String, instances: Vec<Vec<E::Scalar>>) -> Self {
        HostCircuitInfo {
            circuit: c,
            name,
            instances,
        }
    }
}

pub trait Prover<E: MultiMillerLoop> {
    fn create_proof(self, cache_folder: &Path, k: u32) -> Vec<u8>;
    fn mock_proof(&self, k: u32);
}

impl<E: MultiMillerLoop, C: Circuit<E::Scalar>> Prover<E> for HostCircuitInfo<E, C> {
    fn create_proof(self, cache_folder: &Path, k: u32) -> Vec<u8> {
        let params =
            load_or_build_unsafe_params::<E>(k, Some(&cache_folder.join(format!("K{}.params", k))));
        let vkey = load_or_build_vkey::<E, C>(
            &params,
            &self.circuit,
            Some(&cache_folder.join(format!("{}.vkey.data", self.name))),
        );
        let cache_file = &cache_folder.join(format!("{}.transcript.data", self.name));
        let pkey = keygen_pk(&params, vkey, &self.circuit).expect("keygen_pk should not fail");
        let mut transcript = PoseidonWrite::init(vec![]);
        let instances: Vec<&[E::Scalar]> =
            self.instances.iter().map(|x| &x[..]).collect::<Vec<_>>();
        create_proof(
            &params,
            &pkey,
            &[self.circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let r = transcript.finalize();
        let mut fd = std::fs::File::create(&cache_file).unwrap();
        fd.write_all(&r).unwrap();
        r
    }

    fn mock_proof(&self, k: u32) {
        let prover = MockProver::run(k, &self.circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
