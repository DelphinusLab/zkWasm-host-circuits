use crate::customized_curcuits;
use crate::table_item;
use crate::item_count;
use crate::utils::GateCell;
use halo2_proofs::arithmetic::FieldExt;
use std::marker::PhantomData;
use halo2_proofs::plonk::{Fixed, Column, Advice, Selector, Expression, VirtualCells};
use halo2_proofs::poly::Rotation;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::circuit::Chip;

customized_curcuits!(MerkleConfig, 2, 7, 6, 0, 1,
    | carry   | left | right | index   | pos   | more   | sel
    | carry_n | nil  | nil   | index_n | pos_n | more_n | nil
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
        let fixed = [];

        let config = MerkleConfig { fixed, selector, witness };

        cs.create_gate("select left right", |meta| {
            let carry = config.get_expr(meta, MerkleConfig::carry());
            let left = config.get_expr(meta, MerkleConfig::left());
            let right = config.get_expr(meta, MerkleConfig::right());
            let index = config.get_expr(meta, MerkleConfig::index());
            let pos = config.get_expr(meta, MerkleConfig::pos());
            let more = config.get_expr(meta, MerkleConfig::more());
            let sel = config.get_expr(meta, MerkleConfig::sel());

            let carry_n = config.get_expr(meta, MerkleConfig::carry_n());
            let index_n = config.get_expr(meta, MerkleConfig::index_n());
            let pos_n = config.get_expr(meta, MerkleConfig::pos_n());
            let more_n = config.get_expr(meta, MerkleConfig::more_n());

            vec![ sel * more
            ]
        });
        config
    }
}


