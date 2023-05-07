use crate::customized_curcuits;
use crate::table_item;
use crate::item_count;
use crate::utils::GateCell;
use std::marker::PhantomData;
use std::fmt::Debug;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Fixed, Column, Advice,
    Selector, Expression, VirtualCells,
    Error,
};
use halo2_proofs::poly::Rotation;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::{Chip, Region, AssignedCell};
use crate::constant_from;
use crate::host::merkle::{MerkleTree, MerkleProof};

customized_curcuits!(MerkleConfig, 2, 8, 6, 1, 1,
    | carry   | left | right | index   | k   | odd   | pos   | sel
    | carry_n | nil  | nil   | nil     | k_n | odd_n | nil   | nil
);


pub struct MerkleChip<F:FieldExt> {
    config: MerkleConfig,
    _marker: PhantomData<F>
}


impl<F: FieldExt> Chip<F> for MerkleChip<F> {
    type Config = MerkleConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> MerkleChip<F> {
    pub fn new(config: MerkleConfig) -> Self {
        MerkleChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> MerkleConfig {
        let witness= [0; 6]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let selector =[cs.selector()];
        let fixed = [cs.fixed_column()];

        let config = MerkleConfig { fixed, selector, witness };

        cs.create_gate("select left right", |meta| {
            let carry = config.get_expr(meta, MerkleConfig::carry());
            let left = config.get_expr(meta, MerkleConfig::left());
            let right = config.get_expr(meta, MerkleConfig::right());
            let odd = config.get_expr(meta, MerkleConfig::odd());
            let sel = config.get_expr(meta, MerkleConfig::sel());

            // if odd then carry is put at right else put at left
            vec![sel * (odd.clone() * (carry.clone() - right) + (constant_from!(1)-odd) * (carry - left))]
        });


        cs.create_gate("calculate offset", |meta| {
            let index = config.get_expr(meta, MerkleConfig::index());
            let pos = config.get_expr(meta, MerkleConfig::pos());
            let odd = config.get_expr(meta, MerkleConfig::odd());
            let sel = config.get_expr(meta, MerkleConfig::sel());
            let k = config.get_expr(meta, MerkleConfig::k());

            let k_n = config.get_expr(meta, MerkleConfig::k_n());
            let odd_n = config.get_expr(meta, MerkleConfig::odd_n());

            vec![
                sel.clone() * (constant_from!(2) * k.clone() + odd + pos.clone() - index),
                sel * pos * (constant_from!(2) * k_n + odd_n - k),
            ]
        });
        config
    }


    fn assign_proof<const D: usize, M: MerkleTree<F, D>>(
        &self,
        region: &mut Region<F>,
        start_offset: usize,
        _merkle: M,
        proof: MerkleProof<F, D>,
    ) -> Result<(), Error> {
        let mut offset = proof.index - (1u32 << D) - 1;
        let mut carry = proof.source;
        for i in 0..D {
            let depth = D-i-1;
            let pos = (1u32 << depth) - 1;
            let index = offset + pos;
            let k = offset/2;
            let odd = offset - (k*2);
            let (left, right) = if odd == 1 { (&proof.assist[i], &carry) } else { (&carry, &proof.assist[i]) };
            self.config.assign_cell(region, start_offset+i, MerkleConfig::pos(), F::from(pos as u64))?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::k(), F::from(k as u64))?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::odd(), F::from(odd as u64))?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::carry(), carry)?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::index(), F::from(index as u64))?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::left(), *left)?;
            self.config.assign_cell(region, start_offset+i, MerkleConfig::right(), *right)?;
            offset = offset/2;
            carry = M::hash(left, right);
        }
        Ok(())
    }
}


