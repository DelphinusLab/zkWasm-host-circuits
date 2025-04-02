pub mod anemoi;
pub mod babyjub;
pub mod bits_arith;
pub mod bls;
pub mod bn256;
pub mod host;
pub mod keccak256;
pub mod merkle;
pub mod poseidon;
pub mod range;
//pub(crate) mod keccak_arith_table;

use crate::utils::{field_to_bn, field_to_u64, GateCell, Limb};

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
    | l0   | l1    | l2   | l3   | d   |  c0  | c1  | c2  | c3  | cd  | cdn | c   | c03  | c12  | lookup_hint | lookup_ind  | common_sel | extension_sel
    | l0_n | l1_n  | l2_n | nil  | d_n |  nil | nil | nil | nil | nil | nil | nil | nil  | nil  | nil         | nil         |    nil     |      nil
);
pub trait LookupAssistConfig {
    /// register a column (col) to be range checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        cs: &mut ConstraintSystem<F>,
        cols: impl Fn(&mut VirtualCells<F>) -> Vec<Expression<F>>,
    );
}

pub trait LookupAssistChip<F: FieldExt> {
    fn provide_lookup_evidence(
        &mut self,
        region: &Region<F>,
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
        shared_advices: &Vec<Column<Advice>>,
    ) -> Self {
        let witness = [
            shared_advices[0].clone(),
            shared_advices[1].clone(),
            shared_advices[2].clone(),
            shared_advices[3].clone(),
            shared_advices[4].clone(),
        ];
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 13].map(|_| cs.fixed_column());
        let selector = [];

        let config = CommonGateConfig {
            fixed,
            selector,
            witness,
        };

        lookup_assist_config.register(cs, |c| {
            vec![
                config.get_expr(c, CommonGateConfig::l0())
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l1())
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l2())
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l3())
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l0().next(2))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l1().next(2))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l2().next(2))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l3().next(2))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l0().next(4))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l1().next(4))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l2().next(4))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::l3().next(4))
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
                config.get_expr(c, CommonGateConfig::lookup_hint())
                    * config.get_expr(c, CommonGateConfig::lookup_ind()),
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
        region: &Region<F>,
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
        region: &Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        limb: &Limb<F>,
        limbs: &mut Vec<Limb<F>>,
        limb_size_raw: usize,
    ) -> Result<(), Error> {
        let limb_size = (limb_size_raw + 3) & (!3);
        let extended_bits = limb_size - limb_size_raw;

        let mut bool_limbs = field_to_bn(&limb.value).to_radix_le(2);
        bool_limbs.truncate(limb_size);
        bool_limbs.resize_with(limb_size, || 0);
        bool_limbs.reverse();

        let mut new_limbs = vec![];

        let f_0 = F::zero();
        let f_1 = F::one();
        let f_n1 = -f_1;
        let f_2 = f_1.double();
        let f_4 = f_2.double();
        let f_8 = f_4.double();
        let f_16 = f_8.double();

        let pick = |x: u8, default| if x == 0 { f_0 } else { default };
        let pick_bit = |x: u8| if x == 0 { f_0 } else { f_1 };

        let mut v = F::zero();
        let lines = limb_size / 4;
        for i in 0..lines {
            let l0 = pick_bit(bool_limbs[4 * i]);
            let l1 = pick_bit(bool_limbs[4 * i + 1]);
            let l2 = pick_bit(bool_limbs[4 * i + 2]);
            let l3 = pick_bit(bool_limbs[4 * i + 3]);

            let mut v_next = v * f_16;
            v_next += pick(bool_limbs[4 * i], f_8);
            v_next += pick(bool_limbs[4 * i + 1], f_4);
            v_next += pick(bool_limbs[4 * i + 2], f_2);
            v_next += pick(bool_limbs[4 * i + 3], f_1);

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
                if i == 0 {
                    // skip the extended bits
                    [
                        if extended_bits < 1 { Some(f_8) } else { None },
                        if extended_bits < 2 { Some(f_4) } else { None },
                        if extended_bits < 3 { Some(f_2) } else { None },
                        if extended_bits < 4 { Some(f_1) } else { None },
                        None,
                        Some(f_n1),
                        None,
                        None,
                        None,
                    ]
                } else {
                    [
                        Some(f_8),
                        Some(f_4),
                        Some(f_2),
                        Some(f_1),
                        Some(f_16),
                        Some(f_n1),
                        None,
                        None,
                        None,
                    ]
                },
                0,
            )?;
            if i == 0 {
                new_limbs.append(&mut l[extended_bits..4].to_vec());
            } else {
                new_limbs.append(&mut l[0..4].to_vec());
            }
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

        // constraint all the limbs to be either 1 or 0:
        // apply eqn: (val * val) - val = 0,
        // by: (ws[1] * ws[2] * cs[7]) + (ws[0] * cs[0]) = 0,
        for lm in new_limbs.clone() {
            self.assign_line(
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

        limbs.append(&mut new_limbs);
        Ok(())
    }

    /// decompose a limb into bytes cells, in little endian
    /// return (a, [a0,a1,a2,a3,a4,a5,a6,a7])
    pub fn decompose_bytes<F: FieldExt>(
        &self,
        region: &Region<F>,
        offset: &mut usize,
        limb: &Limb<F>,
        rotate: usize, //how limbs rotated towards high bits
        hint: u64,     // lookup hints
    ) -> Result<(Limb<F>, [Limb<F>; 8]), Error> {
        assert!(rotate < 8);
        let rot = |x| (x + ((8 - rotate) as usize)) % 8;

        let limbu64 = field_to_u64(&limb.value);
        let bytes = limbu64.to_le_bytes().map(|x| x as u64);
        let mut mid = 0;
        for i in 0..4 {
            mid += bytes[rot(i)] * 256u64.pow(rot(i) as u32)
        }
        let mid_f = Limb::new(None, F::from(limbu64 - (mid as u64)));

        let bytes_f = bytes.map(|x| Limb::new(None, F::from(x as u64)));

        let c = self.assign_line(
            region,
            &mut (),
            offset,
            [
                Some(bytes_f[rot(0)].clone()),
                Some(bytes_f[rot(1)].clone()),
                Some(bytes_f[rot(2)].clone()),
                Some(bytes_f[rot(3)].clone()),
                Some(limb.clone()),
                Some(mid_f.clone()),
            ],
            [
                Some(F::from(256u64.pow(rot(0) as u32))),
                Some(F::from(256u64.pow(rot(1) as u32))),
                Some(F::from(256u64.pow(rot(2) as u32))),
                Some(F::from(256u64.pow(rot(3) as u32))),
                Some(-F::one()),
                Some(F::one()),
                None,
                None,
                None,
            ],
            hint,
        )?;

        let d = self.assign_line(
            region,
            &mut (),
            offset,
            [
                Some(bytes_f[rot(4)].clone()),
                Some(bytes_f[rot(5)].clone()),
                Some(bytes_f[rot(6)].clone()),
                Some(bytes_f[rot(7)].clone()),
                Some(mid_f),
                None,
            ],
            [
                Some(F::from(256u64.pow(rot(4) as u32))),
                Some(F::from(256u64.pow(rot(5) as u32))),
                Some(F::from(256u64.pow(rot(6) as u32))),
                Some(F::from(256u64.pow(rot(7) as u32))),
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            hint,
        )?;
        Ok((
            c[4].clone(),
            [
                c[0].clone(),
                c[1].clone(),
                c[2].clone(),
                c[3].clone(),
                d[0].clone(),
                d[1].clone(),
                d[2].clone(),
                d[3].clone(),
            ],
        ))
    }

    /// put pure witness advices with no constraints.
    fn assign_witness<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &Region<F>,
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

    fn assign_line<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        value: [Option<Limb<F>>; 6],
        coeffs: [Option<F>; 9],
        hint: u64, // the boundary limit of the first cell
    ) -> Result<Vec<Limb<F>>, Error> {
        #[cfg(debug_assertions)]
        {
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
        }

        let mut limbs = vec![];
        for i in 0..6 {
            match &value[i] {
                Some(x) => {
                    let limb = self
                        .assign_cell(region, *offset, &COMMON_WITNESS[i], x.value)
                        .unwrap();
                    x.cell.as_ref().map(|c| {
                        region
                            .constrain_equal(limb.get_the_cell().cell(), c.cell())
                            .unwrap();
                    });
                    limbs.push(limb);
                }
                None => {}
            }
        }

        for i in 0..9 {
            match &coeffs[i] {
                Some(v) => {
                    if !v.is_zero_vartime() {
                        self.assign_cell(region, *offset, &COMMON_CS[i], *v)
                            .unwrap();
                    }
                }
                _ => {}
            }
        }

        self.assign_cell(region, *offset, &CommonGateConfig::common_sel(), F::one())?;

        if hint != 0 {
            self.assign_cell(
                region,
                *offset,
                &CommonGateConfig::lookup_hint(),
                F::from(hint),
            )?;
            self.assign_cell(region, *offset, &CommonGateConfig::lookup_ind(), F::one())?;
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
        region: &Region<F>,
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
        region: &Region<F>,
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

    // Support to return inputs' cells and add eq_constraints for res
    fn sum_with_constant_ext<F: FieldExt, LC: LookupAssistChip<F>, LB>(
        &self,
        region: &Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        inputs: Vec<(LB, F)>,
        constant: Option<F>,
        expected_res: Option<&Limb<F>>,
    ) -> Result<(Vec<Limb<F>>, Limb<F>), Error>
    where
        LB: core::borrow::Borrow<Limb<F>>,
    {
        let mut acc = F::zero();
        let mut assigned_res = None;
        let mut assigned_inputs = vec![];

        for (i, chunk) in inputs.chunks(4).enumerate() {
            let result = chunk
                .iter()
                .fold(acc, |acc, (l, v)| acc + l.borrow().value * v);

            let mut limbs = chunk
                .iter()
                .map(|(l, _)| Some(l.borrow().clone()))
                .collect::<Vec<Option<Limb<_>>>>();
            let mut coeffs = chunk
                .iter()
                .map(|(_, v)| Some(v.clone()))
                .collect::<Vec<Option<F>>>();

            let acc_coeff = if i == 0 { None } else { Some(F::one()) };

            if chunk.len() <= 3 {
                // Solve the last parts in one line
                let result = result + constant.unwrap_or(F::zero());
                limbs.resize_with(3, || None);
                coeffs.resize_with(3, || None);
                limbs.append(&mut vec![
                    Some(Limb::new(None, result)),
                    Some(Limb::new(None, acc)),
                    None,
                ]);
                coeffs.append(&mut vec![
                    Some(-F::one()),
                    acc_coeff,
                    None,
                    None,
                    None,
                    constant,
                ]);
            } else {
                limbs.resize_with(4, || None);
                coeffs.resize_with(4, || None);
                limbs.append(&mut vec![
                    Some(Limb::new(None, acc)),
                    Some(Limb::new(None, result)),
                ]);
                coeffs.append(&mut vec![acc_coeff, Some(-F::one()), None, None, None]);
            }

            let cells = self.assign_line(
                region,
                lookup_assist_chip,
                offset,
                limbs.try_into().unwrap(),
                coeffs.try_into().unwrap(),
                0,
            )?;

            let mut it = cells.into_iter();
            for _ in 0..chunk.len() {
                assigned_inputs.push(it.next().unwrap());
            }

            if chunk.len() <= 3 {
                assigned_res = Some(it.next().unwrap());
            } else {
                acc = result;
            }
        }

        let assigned_res = if let Some(assigned_res) = assigned_res {
            assigned_res
        } else {
            let result = acc + constant.map_or(F::zero(), |x| x);
            // collect the last acc as result
            let cells = self.assign_line(
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
            )?;
            cells[0].clone()
        };

        if let Some(expected_res) = expected_res {
            region.constrain_equal(
                expected_res.get_the_cell().cell(),
                assigned_res.get_the_cell().cell(),
            )?;
        }

        Ok((assigned_inputs, assigned_res))
    }

    fn sum_with_constant<F: FieldExt, LC: LookupAssistChip<F>>(
        &self,
        region: &Region<F>,
        lookup_assist_chip: &mut LC,
        offset: &mut usize,
        inputs: Vec<(&Limb<F>, F)>,
        constant: Option<F>,
    ) -> Result<Limb<F>, Error> {
        let (_, res) =
            self.sum_with_constant_ext(region, lookup_assist_chip, offset, inputs, constant, None)?;
        Ok(res)
    }
}
