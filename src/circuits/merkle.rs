use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
};
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
use halo2_proofs::circuit::{Chip, Region, AssignedCell, Layouter};
use halo2_proofs::pairing::bn256::Fr;

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
        select_chip::SelectChip,
    },
};

use crate::constant_from;
use crate::host::merkle::{MerkleTree, MerkleProof};


/* Given a merkel tree eg1:
 * 0
 * 1 2
 * 3 4 5 6
 * 7 8 9 10 11 12 13 14
 * A proof of 7 = {source: 7.hash, root: 0.hash, assist: [8.hash,4.hash,2.hash], index: 7}
 */

customized_circuits!(MerkleConfig, 2, 7, 1, 2,
   | carry   | left | right | index   | k   | odd   | pos   | is_set | sel
   | carry_n | nil  | nil   | nil     | k_n | odd_n | nil   | nil    | nil
);


/*
 * Circuit of eg1 of proof of node 7:
 *
 * 7.hash, left: 7.hash, right: assist[0], index:7, k:0, odd:0, pos:2^{3}-1, is_set, true
 * hash_0, left: hash_0, right: assist[1], index:3, k:0, odd:0, pos:2^{2}-1, is_set, true
 * hash_1, left: hash_1, right: assist[2], index:1, k:0, odd:0, pos:2^{1}-1, is_set, true
 * hash_2                                                                            false
 *
 * index = 2*k + odd + pos
 * k_n * 2 + odd_n = k
 * odd * (carry - right) + (1-odd) * (carry - left) * sel
 * odd * (1-odd) = 0
 *
 * let assigned_cell = hash(left, right) ------> external_circuit return AssignedCell
 * copy_constarint(assigned_cell, carry_n)
 *
 */


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
        let witness= [0; 7]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let selector =[cs.selector(), cs.selector()];
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
        _merkle: &M,
        proof: &MerkleProof<F, D>,
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
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::pos(), F::from(pos as u64))?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::k(), F::from(k as u64))?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::odd(), F::from(odd as u64))?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::carry(), carry)?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::index(), F::from(index as u64))?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::left(), *left)?;
            self.config.assign_cell(region, start_offset+i, &MerkleConfig::right(), *right)?;
            offset = offset/2;
            carry = M::hash(left, right);
        }
        Ok(())
    }

    pub fn assign_get<const D: usize, M: MerkleTree<F, D>>(
        &self,
        region: &mut Region<F>,
        start_offset: usize,
        merkle: &M,
        proof: &MerkleProof<F, D>,
    ) -> Result<(), Error> {
        self.assign_proof(region, start_offset, merkle, proof)
    }

    pub fn assign_set<const D: usize, M: MerkleTree<F, D>>(
        &self,
        region: &mut Region<F>,
        start_offset: usize,
        merkle: &M,
        proof_get: &MerkleProof<F, D>,
        proof_set: &MerkleProof<F, D>,
    ) -> Result<(), Error> {
        self.assign_proof(region, start_offset, merkle, proof_get)?;
        self.assign_proof(region, start_offset, merkle, proof_set)
    }
}

impl super::HostOpSelector for MerkleChip<Fr> {
    type Config = MerkleConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _base_config: &BaseChipConfig,
        _range_config: &RangeChipConfig,
    ) -> Self::Config {
        MerkleChip::<Fr>::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        MerkleChip::new(c)
    }

    fn assign(
        region: &mut Region<Fr>,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        shared_index: &Vec<Fr>,
        filtered_operands: Column<Advice>,
        filtered_opcodes: Column<Advice>,
        filtered_index: Column<Advice>,
        merged_operands: Column<Advice>,
        indicator: Column<Fixed>,
    ) -> Result<Vec<AssignedCell<Fr, Fr>>, Error> {
        let opcodes: Vec<Fr> = vec![
            //Fr::from(BN256OP::BN256ADD as u64),
            //Fr::from(BN256OP::BN256SUM as u64),
        ];
        let mut arg_cells = vec![];
        /* The 0,2,5,7's u54 of every G1(11 * u54) return true, others false  */
        let merge_next = |i: usize| {
            todo!();
        };
        let mut offset = 0;
        let mut picked_offset = 0;
        let mut toggle: i32 = -1;
        for opcode in shared_opcodes {
            if opcodes.contains(opcode) {
                region.assign_advice(
                    || "picked operands",
                    filtered_operands,
                    picked_offset,
                    || Ok(shared_operands[offset]),
                )?;

                region.assign_advice(
                    || "picked opcodes",
                    filtered_opcodes,
                    picked_offset,
                    || Ok(opcode.clone()),
                )?;

                region.assign_advice(
                    || "picked index",
                    filtered_index,
                    picked_offset,
                    || Ok(shared_index[offset]),
                )?;

                let value = if toggle >= 0 {
                    shared_operands[offset]
                        .clone()
                        .mul(&Fr::from(1u64 << 32).square())
                        .add(&shared_operands[toggle as usize])
                } else {
                    shared_operands[offset].clone()
                };
                let opcell = region.assign_advice(
                    || "picked merged operands",
                    merged_operands,
                    picked_offset,
                    || Ok(value),
                )?;

                let value = if merge_next(picked_offset) {
                    toggle = offset as i32;
                    Fr::from(1u64 << 54)
                } else {
                    arg_cells.append(&mut vec![opcell]);
                    toggle = -1;
                    Fr::zero()
                };
                region.assign_fixed(|| "indicator", indicator, picked_offset, || Ok(value))?;
                picked_offset += 1;
            };
            offset += 1;
        }
        Ok(arg_cells)
    }

    fn synthesize(
        &self,
        arg_cells: &Vec<AssignedCell<Fr, Fr>>,
        base_chip: &BaseChip<Fr>,
        range_chip: &RangeChip<Fr>,
        point_select_chip: &SelectChip<Fr>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        todo!();
        let len = arg_cells.len();
        //let args = arg_cells[0..len - 7].to_vec();
        //let ret = arg_cells[len - 7..len].to_vec();
        //self.load_bn256_sum_circuit(&args, &ret, &base_chip, &range_chip, &point_select_chip, layouter)?;
        Ok(())
    }
}
