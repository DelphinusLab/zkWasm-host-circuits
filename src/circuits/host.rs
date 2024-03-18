use super::Limb;
use crate::{adaptor::get_selected_entries, constant, utils::GateCell};
use ff::Field;
use halo2_proofs::pairing::bn256::Fr;
use std::marker::PhantomData;

use crate::{
    customized_circuits, customized_circuits_expand, item_count, table_item, value_for_assign,
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};

use crate::constant_from;

#[rustfmt::skip]
customized_circuits!(HostOpConfig, 2, 11, 3, 0,
    | shared_operand | shared_opcode | shared_index   | ops | inv | p1  | filtered_opcode  | filtered_index   | filtered_operand | merged_op   | enable   | indicator | sel_shared | sel
    | nil            | nil           | shared_index_n | nil | nil | nil | nil              | filtered_index_n | nil              | merged_op_n | enable_n | nil       | sel_shared_n | sel_n
);

impl HostOpConfig {
    pub fn configure<F: FieldExt>(&self, cs: &mut ConstraintSystem<F>, opcodes: &Vec<F>) {
        cs.lookup_any("filter-shared-ops", |meta| {
            let sopc = self.get_expr(meta, HostOpConfig::shared_opcode());
            let soper = self.get_expr(meta, HostOpConfig::shared_operand());
            let sidx = self.get_expr(meta, HostOpConfig::shared_index());
            let fopc = self.get_expr(meta, HostOpConfig::filtered_opcode());
            let foper = self.get_expr(meta, HostOpConfig::filtered_operand());
            let fidx = self.get_expr(meta, HostOpConfig::filtered_index());
            let enable = self.get_expr(meta, HostOpConfig::enable());
            vec![
                (fidx * enable.clone(), sidx),
                (foper * enable.clone(), soper),
                (fopc * enable.clone(), sopc),
            ]
        });
        /* we would like to restrict the degree to 4 */
        assert!(opcodes.len() <= 5);

        cs.create_gate("filt ops", |meta| {
            let shared_index = self.get_expr(meta, HostOpConfig::shared_index());
            let shared_index_n = self.get_expr(meta, HostOpConfig::shared_index_n());
            let sopc = self.get_expr(meta, HostOpConfig::shared_opcode());
            let sel = self.get_expr(meta, HostOpConfig::sel_shared());
            let ops = self.get_expr(meta, HostOpConfig::ops());
            let inv = self.get_expr(meta, HostOpConfig::inv());
            let mut cache_ops = constant_from!(1 as u64);
            for i in 0..opcodes.len() {
                if i < 4 {
                    cache_ops = cache_ops * (sopc.clone() - constant!(opcodes[i].clone()));
                }
            }

            let full_ops_mult = if opcodes.len() == 5 {
                ops.clone() * (sopc.clone() - constant!(opcodes[4].clone()))
            } else {
                ops.clone()
            };
            let picked = shared_index.clone() - shared_index_n.clone();

            // degree 3
            let expr = full_ops_mult.clone() * picked.clone() * sel.clone();
            let either_zero =
                (full_ops_mult.clone() * inv + picked - constant_from!(1)) * sel.clone();

            let ops_captures_four = sel.clone() * (ops - cache_ops);
            vec![expr, either_zero, ops_captures_four]
        });

        cs.create_gate("shared_index decrease", |meta| {
            let shared_index = self.get_expr(meta, HostOpConfig::shared_index());
            let shared_index_n = self.get_expr(meta, HostOpConfig::shared_index_n());
            let sel = self.get_expr(meta, HostOpConfig::sel());
            vec![
                sel.clone()
                    * (shared_index.clone() - shared_index_n.clone() - constant_from!(1 as u64))
                    * (shared_index - shared_index_n),
            ]
        });

        cs.create_gate("filtered_index decrease", |meta| {
            let filtered_index = self.get_expr(meta, HostOpConfig::filtered_index());
            let filtered_index_n = self.get_expr(meta, HostOpConfig::filtered_index_n());
            let sel = self.get_expr(meta, HostOpConfig::sel());
            vec![
                sel.clone()
                    * (filtered_index.clone()
                        - filtered_index_n.clone()
                        - constant_from!(1 as u64))
                    * filtered_index_n.clone(),
                sel.clone()
                    * (filtered_index.clone()
                        - filtered_index_n.clone()
                        - constant_from!(1 as u64))
                    * filtered_index,
            ]
        });

        cs.create_gate("merge operands in filtered columns", |meta| {
            let merged_op = self.get_expr(meta, HostOpConfig::merged_op());
            let merged_op_n = self.get_expr(meta, HostOpConfig::merged_op_n());
            let cur_op = self.get_expr(meta, HostOpConfig::filtered_operand());
            let indicator = self.get_expr(meta, HostOpConfig::indicator());
            vec![indicator.clone() * (merged_op - (merged_op_n * indicator + cur_op))]
            // merged_op_n * indicator + cur_op == merged_op ???
        });

        /* enable is continuous with pattern 1,1,1,1,1,0,0,0,0 when sel is active */
        cs.create_gate("enable consistant", |meta| {
            let enable = self.get_expr(meta, HostOpConfig::enable());
            let enable_n = self.get_expr(meta, HostOpConfig::enable_n());
            let sel = self.get_expr(meta, HostOpConfig::sel());
            vec![(enable.clone() - constant_from!(1 as u64)) * enable_n * sel.clone()]
        });

        cs.create_gate("end selector means zero index", |meta| {
            let sel = self.get_expr(meta, HostOpConfig::sel_shared());
            let shared_index = self.get_expr(meta, HostOpConfig::shared_index());
            let sel_n = self.get_expr(meta, HostOpConfig::sel_shared_n());
            vec![sel * (sel_n - constant_from!(1 as u64)) * shared_index]
        });

        cs.create_gate("end filtered means zero index", |meta| {
            let sel = self.get_expr(meta, HostOpConfig::sel());
            let sel_n = self.get_expr(meta, HostOpConfig::sel_n());
            let enable = self.get_expr(meta, HostOpConfig::enable());
            let filtered_index = self.get_expr(meta, HostOpConfig::filtered_index());
            vec![
                sel.clone() * (constant_from!(1 as u64) - enable.clone()) * filtered_index,
                sel * (sel_n - constant_from!(1 as u64)) * enable,
            ]
        });
    }

    pub fn assign_merged_operands(
        &self,
        region: &Region<Fr>,
        offset: &mut usize,
        values: Vec<&((Fr, Fr), Fr)>, //(operand, opcode), index
        indicator: Fr,
        enable: bool,
    ) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
        let mut rev = values.clone();
        let len = values.len();
        rev.reverse();
        let mut merged_ops = vec![];
        let mut merged_acc = Fr::zero(); // accumulator
        for c in rev.iter() {
            merged_acc = c.0 .0 + merged_acc * indicator;
            merged_ops.push(merged_acc);
        }
        merged_ops.reverse();
        let mut ret = None;
        let mut op = None;
        for (i, (((operand, opcode), index), merged_op)) in
            values.into_iter().zip(merged_ops).enumerate()
        {
            self.assign_cell(region, *offset, &HostOpConfig::filtered_operand(), *operand)?;
            let opc =
                self.assign_cell(region, *offset, &HostOpConfig::filtered_opcode(), *opcode)?;
            self.assign_cell(region, *offset, &HostOpConfig::filtered_index(), *index)?;
            self.assign_cell(
                region,
                *offset,
                &HostOpConfig::enable(),
                Fr::from(enable as u64),
            )?;
            self.assign_cell(region, *offset, &HostOpConfig::sel(), Fr::one())?;
            let limb = self.assign_cell(region, *offset, &HostOpConfig::merged_op(), merged_op)?;
            if i == len - 1 {
                self.assign_cell(region, *offset, &HostOpConfig::indicator(), Fr::zero())?;
            } else {
                self.assign_cell(region, *offset, &HostOpConfig::indicator(), indicator)?;
                if i == 0 {
                    ret = Some(limb);
                    op = Some(opc);
                }
            }
            *offset += 1;
        }
        Ok((ret.unwrap(), op.unwrap()))
    }

    pub fn assign_one_line(
        &self,
        region: &Region<Fr>,
        offset: &mut usize,
        operand: Fr,
        opcode: Fr,
        index: Fr,
        merge: Fr,
        ind: Fr,
        enable: bool,
    ) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
        let r = self.assign_cell(region, *offset, &HostOpConfig::filtered_operand(), operand)?;
        let op = self.assign_cell(region, *offset, &HostOpConfig::filtered_opcode(), opcode)?;
        self.assign_cell(region, *offset, &HostOpConfig::filtered_index(), index)?;
        self.assign_cell(region, *offset, &HostOpConfig::indicator(), ind)?;
        self.assign_cell(region, *offset, &HostOpConfig::merged_op(), merge)?;
        self.assign_cell(
            region,
            *offset,
            &HostOpConfig::enable(),
            Fr::from(enable as u64),
        )?;
        self.assign_cell(region, *offset, &HostOpConfig::sel(), Fr::one())?;
        *offset += 1;
        Ok((r, op))
    }
}

pub trait HostOpSelector {
    type Config: Clone + std::fmt::Debug;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config;
    fn construct(c: Self::Config) -> Self;
    fn opcodes() -> Vec<Fr>;
    fn max_rounds(k: usize) -> usize;
    fn assign(
        region: &Region<Fr>,
        k: usize,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error>;
    fn synthesize(
        &mut self,
        offset: &mut usize,
        arg_cells: &Vec<Limb<Fr>>,
        region: &Region<Fr>,
    ) -> Result<(), Error>;
    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error>;
}

pub struct HostOpChip<F: FieldExt, S: HostOpSelector> {
    pub config: HostOpConfig,
    pub selector_chip_config: S::Config,
    _marker: PhantomData<(F, S)>,
}

impl<F: FieldExt, S: HostOpSelector> Chip<F> for HostOpChip<F, S> {
    type Config = HostOpConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<S: HostOpSelector> HostOpChip<Fr, S> {
    pub fn construct(config: <Self as Chip<Fr>>::Config, selector_chip_config: S::Config) -> Self {
        Self {
            config,
            selector_chip_config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<Fr>,
        shared_advices: &Vec<Column<Advice>>,
    ) -> <Self as Chip<Fr>>::Config {
        let witness = [
            cs.named_advice_column("shared_operands".to_string()),
            cs.named_advice_column("shared_opcodes".to_string()),
            cs.named_advice_column("shared_index".to_string()),
            cs.advice_column(),
            cs.advice_column(),
            shared_advices[0].clone(),
            shared_advices[1].clone(),
            shared_advices[2].clone(),
            shared_advices[3].clone(),
            shared_advices[4].clone(),
            shared_advices[5].clone(),
        ];
        witness.map(|x| cs.enable_equality(x));
        let fixed = [cs.fixed_column(), cs.fixed_column(), cs.fixed_column()];
        fixed.map(|x| cs.enable_equality(x));
        let selector = [];

        let config = HostOpConfig::new(witness, fixed, selector);
        config.configure(cs, &S::opcodes());
        config
    }

    pub fn assign(
        &self,
        region: &Region<Fr>,
        k: usize,
        arg_offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let selected_length =
            get_selected_entries(shared_operands, shared_opcodes, &S::opcodes()).len();
        let get_ops = |op| {
            let mut mult = Fr::one();
            for i in S::opcodes().iter().take(4) {
                mult = mult * (op - i)
            }

            let inv: Option<Fr> = S::opcodes()
                .iter()
                .skip(4)
                .fold(mult.clone(), |acc, x| acc * (op - x))
                .invert()
                .into();
            (mult, inv.unwrap_or(Fr::one()))
        };

        let (default_mult, default_inv) = get_ops(Fr::zero());
        let mut offset = 0;
        let mut index = selected_length;
        self.config
            .assign_cell(region, offset, &HostOpConfig::shared_opcode(), Fr::zero())?;

        self.config
            .assign_cell(region, offset, &HostOpConfig::shared_operand(), Fr::zero())?;

        self.config
            .assign_cell(region, offset, &HostOpConfig::shared_operand(), Fr::zero())?;

        self.config
            .assign_cell(region, offset, &HostOpConfig::ops(), default_mult)?;

        self.config
            .assign_cell(region, offset, &HostOpConfig::inv(), default_inv)?;

        let active_total_index = self.config.assign_cell(
            region,
            offset,
            &HostOpConfig::shared_index(),
            Fr::from(index as u64),
        )?;

        let selected_total_index = self.config.assign_cell(
            region,
            offset,
            &HostOpConfig::filtered_index(),
            Fr::from(index as u64),
        )?;

        // Constraint that the selected and active ops are the same
        region.constrain_equal(
            active_total_index.get_the_cell().cell(),
            selected_total_index.get_the_cell().cell(),
        )?;

        offset += 1;
        for opcode in shared_opcodes {
            self.config.assign_cell(
                region,
                offset,
                &HostOpConfig::shared_opcode(),
                opcode.clone(),
            )?;
            self.config.assign_cell(
                region,
                offset,
                &HostOpConfig::shared_operand(),
                shared_operands[offset - 1],
            )?;
            self.config.assign_cell(
                region,
                offset,
                &HostOpConfig::shared_index(),
                Fr::from(index as u64),
            )?;
            let (mult, inv) = get_ops(opcode.clone());

            self.config
                .assign_cell(region, offset, &HostOpConfig::ops(), mult)?;

            self.config
                .assign_cell(region, offset, &HostOpConfig::inv(), inv)?;

            offset += 1;
            if S::opcodes().contains(&opcode) {
                index -= 1;
            }
        }

        let last_row = (1 << 22) - 1000;

        // Set the max sel for shared_ops
        for i in 0..last_row {
            self.config
                .assign_cell(region, i, &HostOpConfig::sel_shared(), Fr::one())?;
            if i >= offset {
                self.config
                    .assign_cell(region, i, &HostOpConfig::ops(), default_mult)?;

                self.config
                    .assign_cell(region, i, &HostOpConfig::inv(), default_inv)?;
            }
        }

        let mut local_offset = *arg_offset;
        let arg_cells = S::assign(
            region,
            k,
            &mut local_offset,
            shared_operands,
            shared_opcodes,
            &self.config,
        )?;
        *arg_offset = local_offset;
        Ok(arg_cells)
    }
}
