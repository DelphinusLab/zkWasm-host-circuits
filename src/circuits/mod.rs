pub mod babyjub;
pub mod bls;
pub mod bn256;
pub mod host;
pub mod merkle;
pub mod modexp;
pub mod poseidon;
pub mod range;
pub mod rmd160;

use crate::utils::{field_to_bn, GateCell, Limb};

use crate::{
    customized_circuits, customized_circuits_expand, item_count, table_item, value_for_assign,
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};

/*
 * Customized gates for some of the common host circuits.
 * lookup_hint: lookup information that is usually combined with l0
 * lookup_ind: whether perform lookup at this line
 */
#[rustfmt::skip]
customized_circuits!(CommonGateConfig, 2, 5, 13, 0,
    | l0   | l1    | l2   | l3   | d   |  c0  | c1  | c2  | c3  | cd  | cdn | c   | c03  | c12  | lookup_hint | lookup_ind  | common_sel | permute_sel 
    | l0_n | l1_n  | l2_n | nil  | d_n |  nil | nil | nil | nil | nil | nil | nil | nil  | nil  | nil         | nil         |    nil     |      nil
);
pub trait LookupAssistConfig {
    /// register a column (col) to be range checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        cs: &mut ConstraintSystem<F>,
        col: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        sz: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    );
}

pub trait LookupAssistChip<F: FieldExt> {
    fn provide_lookup_evidence(
        &mut self,
        region: &mut Region<F>,
        value: F,
        sz: u64,
    ) -> Result<(), Error>;
}

lazy_static::lazy_static! {
    static ref COMMON_WITNESS: [GateCell;6] = [
        CommonGateConfig::l0(),
        CommonGateConfig::l1(),
        CommonGateConfig::l2(),
        CommonGateConfig::l3(),
        CommonGateConfig::d(),
        CommonGateConfig::d_n(),
    ];
    static ref COMMON_CS: [GateCell; 9] = [
        CommonGateConfig::c0(),
        CommonGateConfig::c1(),
        CommonGateConfig::c2(),
        CommonGateConfig::c3(),
        CommonGateConfig::cd(),
        CommonGateConfig::cdn(),
        CommonGateConfig::c03(),
        CommonGateConfig::c12(),
        CommonGateConfig::c(),
    ];
}

impl CommonGateConfig {
    pub fn configure<F: FieldExt, LC: LookupAssistConfig>(
        cs: &mut ConstraintSystem<F>,
        lookup_assist_config: &LC,
    ) -> Self {
        let witness = [0; 5].map(|_| cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 13].map(|_| cs.fixed_column());
        let selector = [];

        let config = CommonGateConfig {
            fixed,
            selector,
            witness,
        };

        lookup_assist_config.register(
            cs,
            |c| {
                config.get_expr(c, CommonGateConfig::l0())
                    * config.get_expr(c, CommonGateConfig::lookup_ind())
            },
            |c| config.get_expr(c, CommonGateConfig::lookup_hint()),
        );

        cs.create_gate("poseidon-2 permute helper constraint", |meta| {
            let x0 = config.get_expr(meta, CommonGateConfig::l0());
            let x1 = config.get_expr(meta, CommonGateConfig::l1());
            let x2 = config.get_expr(meta, CommonGateConfig::l2());
            let x0_2 = config.get_expr(meta, CommonGateConfig::l3());
            let x0_5_c = config.get_expr(meta, CommonGateConfig::d());

            let x0_next = config.get_expr(meta, CommonGateConfig::l0_n());
            let x1_next = config.get_expr(meta, CommonGateConfig::l1_n());
            let x2_next = config.get_expr(meta, CommonGateConfig::l2_n());

            let c = config.get_expr(meta, CommonGateConfig::cd());
            let c0 = config.get_expr(meta, CommonGateConfig::c0());
            let c1 = config.get_expr(meta, CommonGateConfig::c1());
            let c2 = config.get_expr(meta, CommonGateConfig::c2());
            let e1 = config.get_expr(meta, CommonGateConfig::c3());
            let e2 = config.get_expr(meta, CommonGateConfig::c());

            let sel = config.get_expr(meta, CommonGateConfig::permute_sel());

            vec![
                sel.clone() * (x0.clone() * x0.clone() - x0_2.clone()),
                sel.clone() * (x0_2.clone() * x0_2.clone() * x0 + c - x0_5_c.clone()),
                sel.clone() * (x0_next - (x0_5_c.clone() * c0 + x1.clone() * c1 + x2.clone() * c2)),
                sel.clone() * (x1_next - (x0_5_c.clone() * e1 + x1)),
                sel.clone() * (x2_next - (x0_5_c * e2 + x2)),
            ]
        });

        // helper gates for implementing poseidon with 2 cell permute
        cs.create_gate("one line constraint", |meta| {
            let l0 = config.get_expr(meta, CommonGateConfig::l0());
            let l1 = config.get_expr(meta, CommonGateConfig::l1());
            let l2 = config.get_expr(meta, CommonGateConfig::l2());
            let l3 = config.get_expr(meta, CommonGateConfig::l3());
            let d = config.get_expr(meta, CommonGateConfig::d());
            let dnext = config.get_expr(meta, CommonGateConfig::d_n());
            let c0 = config.get_expr(meta, CommonGateConfig::c0());
            let c1 = config.get_expr(meta, CommonGateConfig::c1());
            let c2 = config.get_expr(meta, CommonGateConfig::c2());
            let c3 = config.get_expr(meta, CommonGateConfig::c3());
            let c = config.get_expr(meta, CommonGateConfig::c());
            let cd = config.get_expr(meta, CommonGateConfig::cd());
            let cdn = config.get_expr(meta, CommonGateConfig::cdn());
            let c03 = config.get_expr(meta, CommonGateConfig::c03());
            let c12 = config.get_expr(meta, CommonGateConfig::c12());
            let sel = config.get_expr(meta, CommonGateConfig::common_sel());

            // if odd then carry is put at right else put at left
            vec![
                sel * (l0.clone() * c0
                    + l1.clone() * c1
                    + l2.clone() * c2
                    + l3.clone() * c3
                    + d * cd
                    + dnext * cdn
                    + l0 * l3 * c03
                    + l1 * l2 * c12
                    + c),
            ]
        });

        config
    }

    /// Select between f and t: if cond then t else f
    pub fn select<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        cond: &Limb<F>,
        f: &Limb<F>,
        t: &Limb<F>,
        hint: u64,
    ) -> Result<Limb<F>, Error> {
        let result = if cond.value == F::zero() {
            Limb::new(None, f.value.clone())
        } else {
            Limb::new(None, t.value.clone())
        };
        let l = self.assign_line(
            region,
            lookup_assist_chip,
            offset,
            [
                Some(t.clone()),
                Some(f.clone()),
                Some(cond.clone()),
                Some(cond.clone()),
                Some(result.clone()),
                None,
            ],
            [
                None,
                Some(F::one()),
                None,
                None,
                Some(-F::one()),
                None,
                Some(F::one()),
                Some(-F::one()),
                None,
            ],
            hint,
        )?;
        Ok(l[4].clone())
    }

    ///
    /// decompose a limb into binary cells, in big endian
    /// limbsize needs to be a multiple of 4
    pub fn decompose_limb<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        limb: &Limb<F>,
        limbs: &mut Vec<Limb<F>>,
        limbsize: usize,
    ) -> Result<(), Error> {
        let mut bool_limbs = field_to_bn(&limb.value).to_radix_le(2);
        bool_limbs.truncate(limbsize);
        bool_limbs.resize_with(limbsize, || 0);
        bool_limbs.reverse();
        let mut v = F::zero();
        for i in 0..(limbsize / 4) {
            let l0 = F::from_u128(bool_limbs[4 * i] as u128);
            let l1 = F::from_u128(bool_limbs[4 * i + 1] as u128);
            let l2 = F::from_u128(bool_limbs[4 * i + 2] as u128);
            let l3 = F::from_u128(bool_limbs[4 * i + 3] as u128);
            let v_next = v * F::from_u128(16u128)
                + l0 * F::from_u128(8u128)
                + l1 * F::from_u128(4u128)
                + l2 * F::from_u128(2u128)
                + l3 * F::from_u128(1u128);
            let l = self.assign_line(
                region,
                lookup_assist_chip,
                offset,
                [
                    Some(Limb::new(None, l0)),
                    Some(Limb::new(None, l1)),
                    Some(Limb::new(None, l2)),
                    Some(Limb::new(None, l3)),
                    Some(Limb::new(None, v)),
                    Some(Limb::new(None, v_next)),
                ],
                [
                    Some(F::from_u128(8u128)),
                    Some(F::from_u128(4u128)),
                    Some(F::from_u128(2u128)),
                    Some(F::from_u128(1u128)),
                    Some(F::from_u128(16u128)),
                    Some(-F::one()),
                    None,
                    None,
                    None,
                ],
                0,
            )?;
            limbs.append(&mut l.to_vec()[0..4].to_vec());
            v = v_next;
        }
        // constraint that limb.value is equal v_next so that the above limbs is
        // a real decompose of the limb.value
        self.assign_line(
            region,
            lookup_assist_chip,
            offset,
            [
                Some(limb.clone()),
                None,
                None,
                None,
                Some(Limb::new(None, v)),
                None,
            ],
            [
                Some(F::one()),
                None,
                None,
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?;
        /* todo
         * constraint all the limbs to be either 1 or 0
         */

        // apply eqn: (val * val) - val = 0,
        // by: (ws[1] * ws[2] * cs[7]) + (ws[0] * cs[0]) = 0,
        for i in 0..(limbs.len()) {
            let lm = limbs[i].clone();
            let _l = self.assign_line(
                region,
                lookup_assist_chip,
                offset,
                [
                    Some(lm.clone()),
                    Some(lm.clone()),
                    Some(lm),
                    None,
                    None,
                    None,
                ],
                [
                    Some(-F::one()),
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    Some(F::one()),
                    None,
                ],
                0, //what is limbbound
            )?;
        }

        Ok(())
    }

    /// put pure witness advices with no constraints.
    fn assign_witness<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        _lookup_assist_chip: &mut LC,
        offset: &mut usize,
        value: [Option<Limb<F>>; 5],
        hint: u64, // the boundary limit of the first cell
    ) -> Result<Vec<Limb<F>>, Error> {
        let witnesses = [
            CommonGateConfig::l0(),
            CommonGateConfig::l1(),
            CommonGateConfig::l2(),
            CommonGateConfig::l3(),
            CommonGateConfig::d(),
        ];
        let mut limbs = vec![];
        for i in 0..5 {
            let v = value[i].as_ref().map_or(F::zero(), |x| x.value);
            let limb = self.assign_cell(region, *offset, &witnesses[i], v).unwrap();
            value[i].clone().map(|x| {
                limbs.push(limb.clone());
                x.cell.as_ref().map(|c| {
                    region
                        .constrain_equal(limb.get_the_cell().cell(), c.cell())
                        .unwrap();
                });
            });
        }
        self.assign_cell(
            region,
            *offset,
            &CommonGateConfig::lookup_hint(),
            F::from(hint),
        )?;
        self.assign_cell(
            region,
            *offset,
            &CommonGateConfig::lookup_ind(),
            F::from(if hint == 0 { 0u64 } else { 1u64 }),
        )?;

        *offset = *offset + 1;
        Ok(limbs)
    }

    fn assign_permute_helper_line<F: FieldExt, const RATE: usize, const T: usize>(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        state: &mut [Limb<F>; T],
        x5_c_v: F,
        c_v: [F; T],
        e_v: [F; RATE],
        is_first_line: bool,
        is_last_line: bool,
    ) -> Result<(), Error> {
        // currently only supports (2, 3)
        assert!(RATE == 2);
        assert!(T == 3);

        let x = [Self::l0(), Self::l1(), Self::l2()];
        let x0_2 = Self::l3();
        let x0_5_c = Self::d();

        let x5_c = CommonGateConfig::cd();
        let c = [
            CommonGateConfig::c0(),
            CommonGateConfig::c1(),
            CommonGateConfig::c2(),
        ];
        let e = [CommonGateConfig::c3(), CommonGateConfig::c()];

        self.assign_cell(region, *offset, &CommonGateConfig::permute_sel(), F::one())?;

        // assign constants
        for i in 0..RATE {
            self.assign_cell(region, *offset, &e[i], e_v[i])?;
        }

        for i in 0..T {
            self.assign_cell(region, *offset, &c[i], c_v[i])?;
        }

        self.assign_cell(region, *offset, &x5_c, x5_c_v)?;

        // assign current states
        // only assign state at the 1st line of a permute block
        if is_first_line {
            for i in 0..T {
                let x = self.assign_cell(region, *offset, &x[i], state[i].value)?;
                region.constrain_equal(x.get_the_cell().cell(), state[i].get_the_cell().cell())?;
            }
        }

        // assign current states aux
        let x0_2 = self.assign_cell(region, *offset, &x0_2, state[0].value.square())?;
        let x0_5_c = self.assign_cell(
            region,
            *offset,
            &x0_5_c,
            x0_2.value.square() * state[0].value + x5_c_v,
        )?;

        // assign next states
        state[0] = self.assign_cell(
            region,
            *offset + 1,
            &x[0],
            x0_5_c.value * c_v[0] + state[1].value * c_v[1] + state[2].value * c_v[2],
        )?;
        for i in 1..T {
            state[i] = self.assign_cell(
                region,
                *offset + 1,
                &x[i],
                x0_5_c.value * e_v[i - 1] + state[i].value,
            )?;
        }

        if is_last_line {
            *offset = *offset + 2;
        } else {
            *offset = *offset + 1;
        }

        Ok(())
    }

    fn assign_line<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        value: [Option<Limb<F>>; 6],
        coeffs: [Option<F>; 9],
        hint: u64, // the boundary limit of the first cell
    ) -> Result<Vec<Limb<F>>, Error> {
        let ws = value
            .clone()
            .to_vec()
            .iter()
            .map(|x| x.clone().map_or(F::zero(), |x| x.value))
            .collect::<Vec<F>>();
        let cs = coeffs
            .clone()
            .to_vec()
            .iter()
            .map(|x| x.map_or(F::zero(), |x| x))
            .collect::<Vec<F>>();
        assert!(
            ws[0] * cs[0]
                + ws[1] * cs[1]
                + ws[2] * cs[2]
                + ws[3] * cs[3]
                + ws[4] * cs[4]
                + ws[5] * cs[5]
                + ws[0] * ws[3] * cs[6]
                + ws[1] * ws[2] * cs[7]
                + cs[8]
                == F::zero()
        );

        let mut limbs = vec![];
        for i in 0..6 {
            let v = value[i].as_ref().map_or(F::zero(), |x| x.value);
            let limb = self
                .assign_cell(region, *offset, &COMMON_WITNESS[i], v)
                .unwrap();
            value[i].clone().map(|x| {
                limbs.push(limb.clone());
                x.cell.map(|c| {
                    region
                        .constrain_equal(limb.get_the_cell().cell(), c.cell())
                        .unwrap();
                });
            });
        }
        for i in 0..9 {
            let v = coeffs[i].as_ref().map_or(F::zero(), |x| *x);
            self.assign_cell(region, *offset, &COMMON_CS[i], v).unwrap();
        }
        self.assign_cell(region, *offset, &CommonGateConfig::common_sel(), F::one())?;
        self.assign_cell(
            region,
            *offset,
            &CommonGateConfig::lookup_hint(),
            F::from(hint),
        )?;
        self.assign_cell(
            region,
            *offset,
            &CommonGateConfig::lookup_ind(),
            F::from(if hint == 0 { 0u64 } else { 1u64 }),
        )?;

        if hint != 0 {
            lookup_assist_chip.provide_lookup_evidence(
                region,
                value[0].as_ref().unwrap().value,
                hint,
            )?;
        };

        *offset = *offset + 1;
        Ok(limbs)
    }

    /// check if limb is equal to constant F
    pub fn eq_constant<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        limb: &Limb<F>,
        constant: &F,
    ) -> Result<Limb<F>, Error> {
        let delta = limb.value - constant;
        // ((limb.value - constant) * r)
        // ((inv * (limb.value - constant)) - (1-r))
        let (inv, r) = if delta.is_zero_vartime() {
            (F::one(), F::one())
        } else {
            (delta.invert().unwrap(), F::zero())
        };
        let diff = self.sum_with_constant(
            region,
            lookup_assist_chip,
            offset,
            vec![(limb, F::one())],
            Some(-constant.clone()),
        )?;
        let r = self.assign_line(
            region,
            lookup_assist_chip,
            offset,
            [
                Some(diff.clone()),
                None,
                None,
                Some(Limb::new(None, r)),
                None,
                None,
            ],
            [
                None,
                None,
                None,
                None,
                None,
                None,
                Some(F::one()),
                None,
                None,
            ],
            0,
        )?;
        let r = r[1].clone();
        let l = self.assign_line(
            region,
            lookup_assist_chip,
            offset,
            [
                Some(Limb::new(None, inv)),
                Some(r),
                None,
                Some(diff),
                None,
                None,
            ],
            [
                None,
                Some(F::one()),
                None,
                None,
                None,
                None,
                Some(F::one()),
                None,
                Some(-F::one()),
            ],
            0,
        )?;
        Ok(l[1].clone())
    }

    pub fn assign_constant<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        value: &F,
    ) -> Result<Limb<F>, Error> {
        let l = self.assign_line(
            region,
            lookup_assist_chip,
            offset,
            [
                Some(Limb::new(None, value.clone())),
                None,
                None,
                None,
                None,
                None,
            ],
            [
                Some(F::one()),
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                Some(-value.clone()),
            ],
            0,
        )?;
        Ok(l[0].clone())
    }

    fn sum_with_constant<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &mut Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        inputs: Vec<(&Limb<F>, F)>,
        constant: Option<F>,
    ) -> Result<Limb<F>, Error> {
        let mut acc = F::zero();
        let mut firstline = true;
        let operands = inputs.clone();
        let mut r = None;
        for chunk in operands.chunks(4) {
            let result = chunk.iter().fold(acc, |acc, &(l, v)| acc + l.value * v);
            if inputs.len() <= 3 {
                // solve it in oneline
                let result = result + constant.map_or(F::zero(), |x| x);
                let mut limbs = chunk
                    .iter()
                    .map(|&(l, _v)| Some(l.clone()))
                    .collect::<Vec<Option<Limb<_>>>>();
                let mut coeffs = chunk
                    .iter()
                    .map(|&(_l, v)| Some(v.clone()))
                    .collect::<Vec<Option<F>>>();
                limbs.resize_with(3, || None);
                coeffs.resize_with(3, || None);
                limbs.append(&mut vec![
                    Some(Limb::new(None, result)),
                    Some(Limb::new(None, acc)),
                    None,
                ]);
                coeffs.append(&mut vec![
                    Some(-F::one()),
                    if firstline { None } else { Some(F::one()) },
                    None,
                    None,
                    None,
                    constant,
                ]);
                let l = self.assign_line(
                    region,
                    lookup_assist_chip,
                    offset,
                    limbs.try_into().unwrap(),
                    coeffs.try_into().unwrap(),
                    0,
                )?;
                r = Some(l.get(l.len() - 2).unwrap().clone());
            } else {
                let mut limbs = chunk
                    .iter()
                    .map(|&(l, _v)| Some(l.clone()))
                    .collect::<Vec<Option<Limb<_>>>>();
                let mut coeffs = chunk
                    .iter()
                    .map(|&(_l, v)| Some(v.clone()))
                    .collect::<Vec<Option<F>>>();
                limbs.resize_with(4, || None);
                coeffs.resize_with(4, || None);
                limbs.append(&mut vec![
                    Some(Limb::new(None, acc)),
                    Some(Limb::new(None, result)),
                ]);
                coeffs.append(&mut vec![Some(F::one()), Some(-F::one()), None, None, None]);
                self.assign_line(
                    region,
                    lookup_assist_chip,
                    offset,
                    limbs.try_into().unwrap(),
                    coeffs.try_into().unwrap(),
                    0,
                )?;
            }
            acc = result;
            firstline = false;
        }
        Ok(r.unwrap_or_else(|| {
            let result = acc + constant.map_or(F::zero(), |x| x);
            // collect the last acc as result
            self.assign_line(
                region,
                lookup_assist_chip,
                offset,
                [
                    Some(Limb::new(None, result)),
                    None,
                    None,
                    None,
                    Some(Limb::new(None, acc)),
                    None,
                ],
                [
                    Some(-F::one()),
                    None,
                    None,
                    None,
                    Some(F::one()),
                    None,
                    None,
                    None,
                    constant,
                ],
                0,
            )
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
        }))
    }
}
