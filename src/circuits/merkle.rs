// The constraint system matrix for an arity-2 Merkle tree of 8 leaves using a mocked hasher (one
// selector/gate `s_hash` and one allocation `digest = (l + GAMMA) * (r + GAMMA)` for a random
// gamma and Merkle left/right inputs `l` and `r`).

// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// | row ||       a_col      |       b_col      |  c_col   | pub_col | s_pub | s_bool  | s_swap | s_hash |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
// |  0  ||       leaf       |      elem_1      |  cbit_1  | cbit_1  |   1   |    1    |    1   |    0   |
// |  1  ||    leaf/elem_1   |   leaf/elem_1    | digest_1 |         |   0   |    0    |    0   |    1   |
// |  2  ||     digest_1*    |      elem_2      |  cbit_2  | cbit_2  |   1   |    1    |    1   |    0   |
// |  3  || digest_1/elem_2  | digest_1/elem_2  | digest_2 |         |   0   |    0    |    0   |    1   |
// |  4  ||     digest_2*    |       elem_3     |  cbit_3  | cbit_3  |   1   |    1    |    1   |    0   |
// |  5  || digest_2/elem_3  | digest_2/elem_3  | digest_3 |  root   |   1   |    0    |    0   |    1   |
// |-----||------------------|------------------|----------|---------|-------|---------|--------|--------|
//   "*" = copy
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, AssignedCell},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Instance,
        Selector,
    },
    poly::Rotation,
};

use std::marker::PhantomData;

// The number of leafs in the Merkle tree. This value can be changed to any power of two.
const N_LEAFS: usize = 8;
const PATH_LEN: usize = N_LEAFS.trailing_zeros() as usize;

// This serves as a mock hash function because the Poseidon chip has not yet been implemented.
fn mock_hash<Fp: FieldExt>(a: Fp, b: Fp) -> Fp {
    a * b
}

enum MaybeAlloc<Fp:FieldExt> {
    Alloc(AssignedCell<Fp, Fp>),
    Unalloc(Fp),
}

impl<Fp: FieldExt> MaybeAlloc<Fp> {
    fn value(&self) -> Fp {
        match self {
            MaybeAlloc::Alloc(alloc) => *alloc.value().unwrap(),
            MaybeAlloc::Unalloc(value) => value.clone(),
        }
    }

    fn cell(&self) -> Cell {
        match self {
            MaybeAlloc::Alloc(alloc) => alloc.cell(),
            MaybeAlloc::Unalloc(_) => unreachable!(),
        }
    }
}

pub struct MerkleChip<Fp: FieldExt> {
    config: MerkleChipConfig,
    _marker: PhantomData<Fp>,
}

#[derive(Clone, Debug)]
pub struct MerkleChipConfig {
    a_col: Column<Advice>,
    b_col: Column<Advice>,
    c_col: Column<Advice>,
    pub_col: Column<Instance>,
    s_pub: Selector,
    s_bool: Selector,
    s_swap: Selector,
    s_hash: Selector,
    //perm_digest: Permutation,
}

impl<Fp: FieldExt> Chip<Fp> for MerkleChip<Fp> {
    type Config = MerkleChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt> MerkleChip<Fp> {
    pub fn new(config: MerkleChipConfig) -> Self {
        MerkleChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fp>) -> MerkleChipConfig {
        let a_col = cs.advice_column();
        let b_col = cs.advice_column();
        let c_col = cs.advice_column();
        let pub_col = cs.instance_column();

        let s_pub = cs.selector();
        let s_bool = cs.selector();
        let s_swap = cs.selector();
        let s_hash = cs.selector();

        cs.create_gate("public input", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let pi = cs.query_instance(pub_col, Rotation::cur());
            let s_pub = cs.query_selector(s_pub);
            vec![s_pub * (c - pi)]
        });

        cs.create_gate("boolean constrain", |cs| {
            let c = cs.query_advice(c_col, Rotation::cur());
            let s_bool = cs.query_selector(s_bool);
            vec![s_bool * c.clone() * (Expression::Constant(Fp::one()) - c)]
        });

        // |-------|-------|-------|--------|
        // | a_col | b_col | c_col | s_swap |
        // |-------|-------|-------|--------|
        // |   a   |   b   |  bit  |    1   |
        // |   l   |   r   |       |        |
        // |-------|-------|-------|--------|
        // where:
        //     bit = 0  ==>  l = a, r = b
        //     bit = 1  ==>  l = b, r = a
        //
        // Choose left gate:
        //     logic: let l = if bit == 0 { a } else { b }
        //     poly:  bit * (b - a) - (l - a) = 0
        //
        // Choose right gate:
        //     logic: let r = if bit == 0 { b } else { a }
        //     poly:  bit * (b - a) - (b - r) = 0
        //
        // Swap gate = choose left + choose right:
        //     logic: let (l, r) = if bit == 0 { (a, b) } else { (b, a) }
        //     poly: bit * (b - a) - (l - a) + bit * (b - a) - (b - r) = 0
        //           bit * 2 * (b - a)  - (l - a) - (b - r) = 0
        cs.create_gate("swap", |cs| {
            let a = cs.query_advice(a_col, Rotation::cur());
            let b = cs.query_advice(b_col, Rotation::cur());
            let bit = cs.query_advice(c_col, Rotation::cur());
            let s_swap = cs.query_selector(s_swap);
            let l = cs.query_advice(a_col, Rotation::next());
            let r = cs.query_advice(b_col, Rotation::next());
            vec![s_swap * ((bit * Fp::from(2) * (b.clone() - a.clone()) - (l - a)) - (b - r))]
        });

        // (l + gamma) * (r + gamma) = digest
        cs.create_gate("hash", |cs| {
            let l = cs.query_advice(a_col, Rotation::cur());
            let r = cs.query_advice(b_col, Rotation::cur());
            let digest = cs.query_advice(c_col, Rotation::cur());
            let s_hash = cs.query_selector(s_hash);
            // Todo: Fill hash constraint here
            vec![s_hash * (l * r) - digest]
        });

        MerkleChipConfig {
            a_col,
            b_col,
            c_col,
            pub_col,
            s_pub,
            s_bool,
            s_swap,
            s_hash,
        }
    }

    pub fn assign(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf: Fp,
        path: [Fp; 8],
        c_bits: [Fp; 8],
    ) -> Result<(), Error> {
        let mut layer_digest = self.hash_leaf_layer(
            layouter,
            leaf,
            path.as_ref()[0],
            c_bits.as_ref()[0]
        )?;
        for layer in 1..PATH_LEN {
            layer_digest = self.hash_non_leaf_layer(
                layouter,
                layer_digest,
                path.as_ref()[layer].clone(),
                c_bits.as_ref()[layer].clone(),
                layer,
            )?;
        }
        Ok(())
    }

    fn hash_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf: Fp,
        path_elem: Fp,
        c_bit: Fp,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        self.hash_layer_inner(layouter, MaybeAlloc::Unalloc(leaf), path_elem, c_bit, 0)
    }

    fn hash_non_leaf_layer(
        &self,
        layouter: &mut impl Layouter<Fp>,
        prev_digest: AssignedCell<Fp, Fp>,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        self.hash_layer_inner(layouter, MaybeAlloc::Alloc(prev_digest), path_elem, c_bit, layer)
    }

    fn hash_layer_inner(
        &self,
        layouter: &mut impl Layouter<Fp>,
        leaf_or_digest: MaybeAlloc<Fp>,
        path_elem: Fp,
        c_bit: Fp,
        layer: usize,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let mut digest_alloc: Option<AssignedCell<Fp, Fp>> = None;

        layouter.assign_region(
            || "leaf layer",
            |mut region| {
                let mut row_offset = 0;

                // Allocate in `a_col` either the leaf or reallocate the previous tree layer's
                // calculated digest (stored in the previous row's `c_col`).
                let a_value = leaf_or_digest.value();

                let a_cell = region.assign_advice(
                    || format!("{} (layer {})", if layer == 0 { "leaf" } else { "a" }, layer),
                    self.config.a_col,
                    row_offset,
                    || Ok(a_value),
                )?;

                if layer > 0 {
                    let prev_digest_cell = leaf_or_digest.cell();
                    region.constrain_equal(prev_digest_cell, a_cell.cell())?;
                }

                // Allocate private inputs for this tree layer's path element and challenge bit (in
                // columns `b_col` and `c_col` respectively). Expose the challenge bit as a public
                // input.
                let _elem_cell = region.assign_advice(
                    || format!("path elem (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Ok(path_elem),
                )?;

                let _c_bit_cell = region.assign_advice(
                    || format!("challenge bit (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Ok(c_bit),
                )?;

                // Expose the challenge bit as a public input.
                self.config.s_pub.enable(&mut region, row_offset)?;

                // Boolean constrain the challenge bit.
                self.config.s_bool.enable(&mut region, row_offset)?;

                // Enable the "swap" gate to ensure the correct order of the Merkle hash inputs.
                self.config.s_swap.enable(&mut region, row_offset)?;

                // In the next row, allocate the correctly ordered Merkle hash inputs, calculated digest, and
                // enable the "hash" gate. If this is the last tree layer, expose the calculated
                // digest as a public input for the tree's root.
                row_offset += 1;

                let (preimg_l_value, preimg_r_value): (Fp, Fp) = if c_bit == Fp::zero() {
                    (a_value, path_elem)
                } else {
                    (path_elem, a_value)
                };

                let _preimg_l_cell = region.assign_advice(
                    || format!("preimg_l (layer {})", layer),
                    self.config.a_col,
                    row_offset,
                    || Ok(preimg_l_value),
                )?;

                let _preimg_r_cell = region.assign_advice(
                    || format!("preimage right (layer {})", layer),
                    self.config.b_col,
                    row_offset,
                    || Ok(preimg_r_value),
                )?;

                let digest_value = mock_hash(preimg_l_value, preimg_r_value);

                let digest_cell = region.assign_advice(
                    || format!("digest (layer {})", layer),
                    self.config.c_col,
                    row_offset,
                    || Ok(digest_value),
                )?;

                digest_alloc = Some(digest_cell);

                self.config.s_hash.enable(&mut region, row_offset)?;

                // If the calculated digest is the tree's root, expose it as a public input.
                let digest_is_root = layer == PATH_LEN - 1;
                if digest_is_root {
                    self.config.s_pub.enable(&mut region, row_offset)?;
                }

                Ok(())
            }
        )?;

        Ok(digest_alloc.unwrap())
    }
}
