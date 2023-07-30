use crate::circuits::poseidon::PoseidonChip;
use crate::circuits::poseidon::PoseidonGateConfig;
use crate::circuits::CommonGateConfig;
use crate::utils::bytes_to_field;
use crate::utils::field_to_bytes;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Chip, Region};
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use std::marker::PhantomData;

use crate::circuits::Limb;
use crate::host::merkle::MerkleProof;
use crate::host::poseidon::MERKLE_HASHER_SPEC;
use crate::host::poseidon::POSEIDON_HASHER_SPEC;
use crate::host::ForeignInst::MerkleSet;
use halo2_proofs::pairing::bn256::Fr;

/* Given a merkel tree eg1 with height=3:
 * 0
 * 1 2
 * 3 4 5 6
 * 7 8 9 10 11 12 13 14
 * A proof of 7 = {source: 7.hash, root: 0.hash, assist: [8.hash,4.hash,2.hash], index: 7}
 */

pub struct MerkleProofState<F: FieldExt, const D: usize> {
    pub source: Limb<F>,
    pub root: Limb<F>, // last is root
    pub assist: [Limb<F>; D],
    pub address: Limb<F>,
    pub zero: Limb<F>,
    pub one: Limb<F>,
}

impl<F: FieldExt, const D: usize> MerkleProofState<F, D> {
    fn default() -> Self {
        MerkleProofState {
            source: Limb::new(None, F::zero()),
            root: Limb::new(None, F::zero()),
            address: Limb::new(None, F::zero()),
            assist: [0; D].map(|_| Limb::new(None, F::zero())),
            zero: Limb::new(None, F::zero()),
            one: Limb::new(None, F::one()),
        }
    }
}

pub struct MerkleChip<F: FieldExt, const D: usize> {
    pub config: CommonGateConfig,
    pub extend: PoseidonGateConfig,
    data_hasher_chip: PoseidonChip<F, 9, 8>,
    merkle_hasher_chip: PoseidonChip<F, 3, 2>,
    state: MerkleProofState<F, D>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const D: usize> Chip<F> for MerkleChip<F, D> {
    type Config = CommonGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<const D: usize> MerkleChip<Fr, D> {
    pub fn new(config: CommonGateConfig, extend: PoseidonGateConfig) -> Self {
        MerkleChip {
            merkle_hasher_chip: PoseidonChip::construct(config.clone(), extend.clone(), MERKLE_HASHER_SPEC.clone()),
            data_hasher_chip: PoseidonChip::construct(config.clone(), extend.clone(), POSEIDON_HASHER_SPEC.clone()),
            config,
            extend,
            state: MerkleProofState::default(),
            _marker: PhantomData,
        }
    }

    pub fn proof_height() -> usize {
        D
    }

    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<Fr>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.merkle_hasher_chip.initialize(config, region, offset)?;
        self.data_hasher_chip.initialize(config, region, offset)
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> (CommonGateConfig, PoseidonGateConfig) {
        let config = CommonGateConfig::configure(cs, &());
        let extend = PoseidonGateConfig::configure(cs, &config);
        (config, extend)
    }

    pub fn assign_proof(
        &mut self,
        region: &mut Region<Fr>,
        offset: &mut usize,
        proof: &MerkleProof<[u8; 32], D>,
        opcode: &Limb<Fr>,
        address: &Limb<Fr>,
        root: &Limb<Fr>,
        value: [&Limb<Fr>; 2],
    ) -> Result<(), Error> {
        let is_set = self.config.eq_constant(
            region,
            &mut (),
            offset,
            opcode,
            &Fr::from(MerkleSet as u64),
        )?;
        let fills = proof
            .assist
            .to_vec()
            .iter()
            .map(|x| Some(Limb::new(None, bytes_to_field(&x))))
            .collect::<Vec<_>>();
        let new_assist: Vec<Limb<Fr>> = fills
            .chunks(5)
            .collect::<Vec<_>>()
            .iter()
            .map(|&values| {
                let mut v = values.clone().to_vec();
                v.resize_with(5, || None);
                self.config
                    .assign_witness(region, &mut (), offset, v.try_into().unwrap(), 0)
                    .unwrap()
            })
            .collect::<Vec<Vec<Limb<_>>>>()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let compare_assist = self
            .state
            .assist
            .clone()
            .zip(new_assist.clone().try_into().unwrap())
            .map(|(old, new)| {
                self.config
                    .select(region, &mut (), offset, &is_set, &new, &old, 0)
                    .unwrap()
            });
        for (a, b) in compare_assist.to_vec().into_iter().zip(new_assist) {
            region.constrain_equal(a.get_the_cell().cell(), b.get_the_cell().cell())?;
        }
        self.state.assist = compare_assist.clone();

        let mut positions = vec![];
        let c = self.config.sum_with_constant(
            region,
            &mut (),
            offset,
            vec![(address, Fr::one())],
            Some(-Fr::from((1u64 << D) - 1)),
        )?;
        //println!("offset for position is: {:?}", c.value);
        self.config
            .decompose_limb(region, &mut (), offset, &c, &mut positions, D)?;
        // position = 0 means assist is at right else assist is at left
        let initial_hash = self.data_hasher_chip.get_permute_result(
            region,
            offset,
            &[
                value[0].clone(),
                value[1].clone(),
                self.state.one.clone(),
                self.state.zero.clone(),
                self.state.zero.clone(),
                self.state.zero.clone(),
                self.state.zero.clone(),
                self.state.zero.clone(),
            ],
            &self.state.one.clone(),
        )?;
        assert_eq!(field_to_bytes(&initial_hash.value), proof.source);

        let final_hash = positions.iter().zip(compare_assist.iter().rev()).fold(
            initial_hash,
            |acc, (position, assist)| {
                let left = self
                    .config
                    .select(region, &mut (), offset, &position, &acc, &assist, 0)
                    .unwrap();
                let right = self
                    .config
                    .select(region, &mut (), offset, &position, &assist, &acc, 0)
                    .unwrap();
                let hash = self
                    .merkle_hasher_chip
                    .get_permute_result(region, offset, &[left, right], &self.state.one.clone())
                    .unwrap();
                //println!("position check: {:?} {:?}", acc.clone().value, assist.clone().value);
                hash
            },
        );
        assert_eq!(root.value, final_hash.value);
        region.constrain_equal(
            root.cell.as_ref().unwrap().cell(),
            final_hash.cell.as_ref().unwrap().cell(),
        )?;
        Ok(())
    }
}
