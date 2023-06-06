use crate::utils::{
    GateCell,
    field_to_bn,
    bn_to_field,
};
use crate::{
    customized_circuits,
    table_item,
    item_count,
    customized_circuits_expand,
};
use std::ops::{Mul, Div};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region, AssignedCell},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;

/*
 * Customized gates for modexp
 */
customized_circuits!(ModExpConfig, 2, 5, 9, 1,
   | l0  | l1   | l2  | l3  | d   |  c0  | c1  | c2  | c3  | cd  | cdn | c   | c03  | c12  | sel
   | nil | nil  | nil | nil | d_n |  nil | nil | nil | nil | nil | nil | nil | nil  | nil  | nil
);
pub struct ModExpChip<F:FieldExt> {
    config: ModExpConfig,
    _marker: PhantomData<F>
}

#[derive(Clone, Debug)]
pub struct Limb<F: FieldExt> {
    cell: Option<AssignedCell<F, F>>,
    value: F
}

impl<F: FieldExt> Limb<F> {
    fn new(cell: Option<AssignedCell<F, F>>, value: F) -> Self {
        Limb { cell, value }
    }
}

#[derive(Clone, Debug)]
pub struct Number<F: FieldExt> {
    limbs: [Limb<F>; 4],
}

impl<F: FieldExt> Number<F> {
    fn add(&self, n: &Self) -> Self {
        Number {
            limbs: [
                Limb::new(None, self.limbs[0].value + n.limbs[0].value),
                Limb::new(None, self.limbs[1].value + n.limbs[1].value),
                Limb::new(None, self.limbs[2].value + n.limbs[2].value),
                Limb::new(None, self.limbs[3].value + n.limbs[3].value),
            ]
        }
    }
    fn from_bn(bn: &BigUint) -> Self {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<108));
        let limb1 = (bn - limb0.clone()).div(BigUint::from(1u128<<108)).modpow(&BigUint::from(1u128), &BigUint::from(1u128<<108));
        let limb2 = bn.div(BigUint::from(1u128<<108)).div(BigUint::from(1u128<<108));
        let native = bn.div(field_to_bn(&(-F::one()))) + BigUint::from(1u128);
        Number {
            limbs: [
                Limb::new(None, bn_to_field(&limb0)),
                Limb::new(None, bn_to_field(&limb1)),
                Limb::new(None, bn_to_field(&limb2)),
                Limb::new(None, bn_to_field(&native)),
            ]

        }
    }
    fn to_bn(&self) -> BigUint {
        let limb0 = field_to_bn(&self.limbs[0].value);
        let limb1 = field_to_bn(&self.limbs[1].value);
        let limb2 = field_to_bn(&self.limbs[2].value);
        (limb2 * BigUint::from(1u128<<108) + limb1) * BigUint::from(1u128<<108) + limb0
    }

}

impl<F: FieldExt> Chip<F> for ModExpChip<F> {
    type Config = ModExpConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ModExpChip<F> {
    pub fn new(config: ModExpConfig) -> Self {
        ModExpChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> ModExpConfig {
        let witness= [0; 5]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 9].map(|_| cs.fixed_column());
        let selector =[cs.selector()];

        let config = ModExpConfig { fixed, selector, witness };

        cs.create_gate("one line constraint", |meta| {
            let l0 = config.get_expr(meta, ModExpConfig::l0());
            let l1 = config.get_expr(meta, ModExpConfig::l1());
            let l2 = config.get_expr(meta, ModExpConfig::l2());
            let l3 = config.get_expr(meta, ModExpConfig::l3());
            let d = config.get_expr(meta, ModExpConfig::d());
            let dnext = config.get_expr(meta, ModExpConfig::d_n());
            let c0 = config.get_expr(meta, ModExpConfig::c0());
            let c1 = config.get_expr(meta, ModExpConfig::c1());
            let c2 = config.get_expr(meta, ModExpConfig::c2());
            let c3 = config.get_expr(meta, ModExpConfig::c3());
            let c  = config.get_expr(meta, ModExpConfig::c());
            let cd  = config.get_expr(meta, ModExpConfig::cd());
            let cdn  = config.get_expr(meta, ModExpConfig::cdn());
            let c03 = config.get_expr(meta, ModExpConfig::c03());
            let c12  = config.get_expr(meta, ModExpConfig::c12());
            let sel = config.get_expr(meta, ModExpConfig::sel());

            // if odd then carry is put at right else put at left
            vec![
                sel * (
                    l0.clone() * c0
                +   l1.clone() * c1
                +   l2.clone() * c2
                +   l3.clone() * c3
                +   d  * cd
                +   dnext * cdn
                +   l0 * l3 * c03
                +   l1 * l2 * c12
                +   c)
            ]

        });
        config
    }

    pub fn assign_constant (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.assign_line(region, offset,
                [
                    Some(number.limbs[i].clone()),
                    None,
                    None,
                    None,
                    None,
                    None,
                ],
                [None, None, None, None, None, None, Some(F::from(number.limbs[i].value)), None, None],
            )?;
            limbs.push(l[0].clone())
        }
        Ok(Number {limbs: limbs.try_into().unwrap()})
    }


    pub fn assign_number (
        &self,
        _region: &mut Region<F>,
        _offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        Ok(number)
    }

    fn assign_line (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       value:  [Option<Limb<F>>; 6],
       coeffs: [Option<F>; 9],
    ) -> Result<Vec<Limb<F>>, Error> {
        let ws = value.clone().to_vec().iter()
            .map(|x|x.clone().map_or(F::zero(), |x| x.value))
            .collect::<Vec<F>>();
        let cs = coeffs.clone().to_vec().iter().map(|x| x.map_or(F::zero(), |x| x)).collect::<Vec<F>>();
        assert!(
            ws[0] * cs[0]
            + ws[1] * cs[1]
            + ws[2] * cs[2]
            + ws[3] * cs[3]
            + ws[4] * cs[4]
            + ws[5] * cs[5]
            + ws[0] * ws[3] * cs[6]
            + ws[1] * ws[2] * cs[7]
            + cs[8] == F::zero()
        );

        let witnesses = [
            ModExpConfig::l0(),
            ModExpConfig::l1(),
            ModExpConfig::l2(),
            ModExpConfig::l3(),
            ModExpConfig::d(),
            ModExpConfig::d_n(),
        ];
        let cs = [
            ModExpConfig::c0(),
            ModExpConfig::c1(),
            ModExpConfig::c2(),
            ModExpConfig::c3(),
            ModExpConfig::cd(),
            ModExpConfig::cdn(),
            ModExpConfig::c03(),
            ModExpConfig::c12(),
            ModExpConfig::c(),
        ];


        let mut limbs = vec![];
        for i in 0..6 {
            let v = value[i].as_ref().map_or(F::zero(), |x| x.value);
            let cell = self.config.assign_cell(region, *offset, &witnesses[i], v).unwrap();
            value[i].clone().map(|x| {
                limbs.push(Limb::new(Some(cell.clone()), x.value));
                x.cell.map(|c| {
                    region.constrain_equal(cell.cell(), c.cell()).unwrap();
                });
            });
        }
        for i in 0..9 {
            let v = coeffs[i].as_ref().map_or(F::zero(), |x| *x);
            self.config.assign_cell(region, *offset, &cs[i], v).unwrap();
        }
        self.config.enable_selector(region, *offset, ModExpConfig::sel())?;
        *offset = *offset+1;
        Ok(limbs)
    }


    pub fn mod_add (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let ret = lhs.add(rhs);
        let limbs = ret.limbs.to_vec().into_iter().enumerate().map(|(i, l)| {
            let l = self.assign_line(
                region, offset,
                [Some(lhs.limbs[i].clone()), Some(rhs.limbs[i].clone()), None, None, Some(l), None],
                [Some(F::one()), Some(F::one()), None, None, Some(F::one()), None, None, None, None],
            ).unwrap();
            l[5].clone() // the fifth is the sum result d
        }).collect::<Vec<_>>();
        Ok(Number {limbs: limbs.try_into().unwrap()})
    }

    pub fn mod_native_mul(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        rem: &Number<F>,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let l = self.assign_line(
            region, offset, [
                None,
                Some(lhs.limbs[3].clone()),
                Some(rhs.limbs[3].clone()),
                Some(rem.limbs[3].clone()),
                None,
                None,
            ],
            [None, None, None, Some(-F::one()), None, None, None, None, Some(F::one())],
        )?;
        Ok(l[2].clone())
    }


    pub fn mod_power108m1 (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<[Limb<F>; 4], Error> {
        let value = number.limbs[0].value + number.limbs[1].value + number.limbs[2].value;
        let l = self.assign_line(
            region, offset, [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                Some(number.limbs[2].clone()),
                None,
                Some(Limb::new(None, value)),
                None
            ],
            [Some(F::one()), Some(F::one()), Some(F::one()), None, Some(-F::one()), None, None, None, None],
        )?;
        Ok(l.try_into().unwrap())
    }

    pub fn mod_power216 (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let value = number.limbs[0].value + number.limbs[1].value * (F::from_u128(1u128 << 108));
        let l = self.assign_line(
            region, offset,
            [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                None,
                None,
                Some(Limb::new(None, value)),
                None
            ],
            [Some(F::one()), Some(F::from_u128(1u128 << 108)), None, None, Some(-F::one()), None, None, None, None],
        )?;
        Ok(l[2].clone())
    }


    pub fn mod_power108m1_mul (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let [_, _, _, ml] = self.mod_power108m1(region, offset, lhs)?;
        let [_, _, _, mr] = self.mod_power108m1(region, offset, rhs)?;
        let v = ml.value * mr.value;
        let bn_q = field_to_bn(&v).div(BigUint::from(1u128<<108));
        let bn_r = field_to_bn(&v) - bn_q.clone() * BigUint::from(1u128 << 108);
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));
        let l = self.assign_line(
            region,
            offset,
            [Some(q), Some(ml), Some(mr), Some(r), None, None],
            [Some(F::from_u128(1u128<<108)), None, None, Some(F::one()), None, None, None, Some(-F::one()), None],
        )?;
        Ok(l[3].clone())
    }

    pub fn mod_power216_mul (
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let x0 = lhs.limbs[0].value;
        let x1 = lhs.limbs[1].value;
        let y0 = rhs.limbs[0].value;
        let y1 = rhs.limbs[1].value;

        let mut v =  x0 * y1 + x1 * y0; //0-2^216
        let l = self.assign_line(
            region,
            offset,
            [
                Some(lhs.limbs[0].clone()),   //x0
                Some(lhs.limbs[1].clone()),   //x1
                Some(rhs.limbs[0].clone()),   //y0
                Some(rhs.limbs[1].clone()),   //y1
                Some(Limb::new(None, v)),
                None
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), Some(F::one()), None],
        )?;
        let vcell = l[4].clone();

        //  compute v mod 2^108
        let bn_q = field_to_bn(&v).div(BigUint::from(1u128<<108));
        let bn_r = field_to_bn(&v) - bn_q.clone() * BigUint::from(1u128 << 108);
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));

        let l = self.assign_line(
            region,
            offset,
            [Some(q), Some(vcell), None, Some(r), None, None],
            [Some(F::from_u128(1u128<<108)), Some(-F::one()), None, Some(F::one()), None, None, None, None, None],
        )?;

        let rcell = l[2].clone();

        v = rcell.value * F::from_u128(1u128<<108) + x0 + y0;

        let l = self.assign_line(
            region,
            offset,
            [
                Some(lhs.limbs[0].clone()),
                Some(rcell),
                None,
                Some(rhs.limbs[0].clone()),
                Some(Limb::new(None, v)),
                None
            ],
            [Some(F::one()), Some(F::from_u128(1u128<<108)), None, Some(F::one()), Some(-F::one()), None, None, None, None],
        )?;

        Ok(l[3].clone())
    }

    pub fn mod_power108m1_zero(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        //todo!()
        Ok(())
    }

    pub fn mod_power216_zero(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        //todo!()
        Ok(())
    }

    pub fn mod_mult(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
       modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        /*
         * x0,x1,x2 * y0,y1,y2 = q0,q1,q2 * m0,m1,m2 + r0,r1,r2
         * mod 2^{108}-1:
         *     (x2+x1+x0) * (y0+y1+y2) = (q0+q1+q2) * (m0+m1+m2) + (r0+r1+r2)
         * mod 2^{216}:
         *     (x1*y0 + x0*y1) * 2^216 + x0*y0 = (q0*m1+q1*m0) * 2^{216} + q0*m0 + r1+r0
         * native:
         *    x*y = q*m + r
         */
        let bn_lhs = lhs.to_bn();
        let bn_rhs = rhs.to_bn();
        let bn_mult = bn_lhs.mul(bn_rhs);
        let bn_modulus = modulus.to_bn();
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone()); //div_rem
        let bn_rem = bn_mult - (bn_quotient.clone() * bn_modulus.clone());
        let modulus = self.assign_number(region, offset, Number::from_bn(&bn_modulus))?;
        let rem = self.assign_number(region, offset, Number::from_bn(&bn_rem))?;
        let quotient = self.assign_number(region, offset, Number::from_bn(&bn_quotient))?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, offset, lhs, rhs)?;
        let mod_108m1_rhs = self.mod_power108m1_mul(region, offset, &quotient, &modulus)?;
        let [r0, r1, r2, mod_108m1_rem] = self.mod_power108m1(region, offset, &rem)?;
        self.mod_power108m1_zero(
            region,
            offset,
            vec![mod_108m1_lhs.clone(), mod_108m1_rhs.clone(), mod_108m1_rem.clone()],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, offset, lhs, rhs)?;
        let mod_216_rhs = self.mod_power216_mul(region, offset, &quotient, &modulus)?;
        let mod_216_rem = self.mod_power216(region, offset, &rem)?;
        self.mod_power216_zero(
            region,
            offset,
            vec![mod_216_lhs, mod_216_rhs, mod_216_rem],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_native = self.mod_native_mul(
            region,
            offset,
            &rem,
            &lhs,
            &rhs,
        )?;
        Ok(Number {
            limbs: [r0, r1, r2, mod_native]
        })
    }


    /* decompose a limb into binary cells, in big endian*/
    pub fn decompose_limb(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        limb: &Limb<F>,
        limbs: &mut Vec<Limb<F>>,
        limbsize: usize
    ) -> Result <(), Error> {
        let mut bool_limbs = field_to_bn(&limb.value).to_radix_le(2);
        bool_limbs.truncate(limbsize);
        let exbits = (4 - bool_limbs.len() % 4)%4;            
        if bool_limbs.len() % 4 != 0 {
            bool_limbs.extend(vec![0; (4 - bool_limbs.len() % 4)]);
        } 
        bool_limbs.reverse();
        let mut v = F::zero();

        if field_to_bn(&limb.value) != BigUint::from(0u128) {
            let bll: usize;
            if field_to_bn(&limb.value) != BigUint::from(0u128) { bll = bool_limbs.len() } else { bll = 0;}
            for i in (0..bll).step_by(4) {
                let (l0, l1, l2, l3, cl0, cl1, cl2, cl3, v_next, vext) = match (i, exbits) {
                    // (l0, l1, l2, l3, cl0, cl1, cl2, cl3, v_next, vext)
                    (0, 1) => ( 
                            None,
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 1] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 2] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 3] as u128))),
                            None,
                            Some(F::from_u128(4u128)),
                            Some(F::from_u128(2u128)),
                            Some(F::from_u128(1u128)),
                            v * F::from_u128(16u128)
                                + F::from_u128(bool_limbs[i + 1] as u128) * F::from_u128(4u128)
                                + F::from_u128(bool_limbs[i + 2] as u128) * F::from_u128(2u128)
                                + F::from_u128(bool_limbs[i + 3] as u128) * F::from_u128(1u128),
                            4 - exbits,
                        ),
                    (0, 2) => ( 
                            None,
                            None,
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 2] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 3] as u128))),
                            None,
                            None,
                            Some(F::from_u128(2u128)),
                            Some(F::from_u128(1u128)),
                            v * F::from_u128(16u128)
                                + F::from_u128(bool_limbs[i + 2] as u128) * F::from_u128(2u128)
                                + F::from_u128(bool_limbs[i + 3] as u128) * F::from_u128(1u128),
                            4 - exbits,    
                        ),
                    (0, 3) => ( 
                            None,
                            None,
                            None,
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 3] as u128))),
                            None,
                            None,
                            None,
                            Some(F::from_u128(1u128)),
                            v * F::from_u128(16u128) + F::from_u128(bool_limbs[i + 3] as u128) * F::from_u128(1u128),
                            4 - exbits, 
                        ),
                    _ => (
                            Some(Limb::new(None, F::from_u128(bool_limbs[i] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 1] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 2] as u128))),
                            Some(Limb::new(None, F::from_u128(bool_limbs[i + 3] as u128))),
                            Some(F::from_u128(8u128)),
                            Some(F::from_u128(4u128)),
                            Some(F::from_u128(2u128)),
                            Some(F::from_u128(1u128)),
                            v * F::from_u128(16u128)
                                + F::from_u128(bool_limbs[i] as u128) * F::from_u128(8u128)
                                + F::from_u128(bool_limbs[i + 1] as u128) * F::from_u128(4u128)
                                + F::from_u128(bool_limbs[i + 2] as u128) * F::from_u128(2u128)
                                + F::from_u128(bool_limbs[i + 3] as u128) * F::from_u128(1u128),
                            4,    
                        ),
                };

                let l = self.assign_line(
                    region,
                    offset,
                    [
                        l0,
                        l1,
                        l2,
                        l3,
                        Some(Limb::new(None, v)),
                        Some(Limb::new(None, v_next)),
                    ],
                    [
                        cl0,
                        cl1,
                        cl2,
                        cl3,
                        Some(F::from_u128(16u128)),
                        Some(-F::one()),
                        None, None, None
                    ],
                )?;
                limbs.append(&mut l.to_vec()[0..vext].to_vec());
                v = v_next;
            }
        }

        let _l = self.assert_limbs_bit(region, offset, limbs.to_vec());
        Ok(())
    }


    // Enforces limb value is `0` or `1`.
    fn assert_limbs_bit(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        limbs: Vec<Limb<F>>
    ) -> Result<(), Error> {
        // apply eqn: (val * val) - val = 0,
        // by: (ws[1] * ws[2] * cs[7]) + (ws[0] * cs[0]) = 0,
        // (val * val * 1) + (val * -1) = 0.
        for i in 0..(limbs.len()) {
            let l0 = limbs[i].value;
            let l1 = limbs[i].value;
            let _l = self.assign_line(
                region,
                offset,
                [
                    Some(Limb::new(None, l0)),
                    Some(Limb::new(None, l0)),
                    Some(Limb::new(None, l1)),
                    None,
                    None,
                    None,
                ],
                [
                    Some(-F::one()), None, None, None, None, None,      
                    None,                                               
                    Some(F::one()),                                    
                    None,                                               
                ],
            )?;
        }
        Ok(())
    }

    pub fn select(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        cond: &Limb<F>,
        zero: &Number<F>,
        base: &Number<F>,
    ) -> Result <Number<F>, Error> {
        //c * a + (1-c) * zero
        let result = if cond.value == F::one() {zero.clone()} else {base.clone()};
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.assign_line(region, offset,
                [
                    Some(base.limbs[i].clone()),
                    Some(zero.limbs[i].clone()),
                    Some(cond.clone()),
                    Some(cond.clone()),
                    Some(result.limbs[i].clone()),
                    None,
                ],
                [None, Some(F::one()), None, None, Some(-F::one()), None, None, Some(F::one()), Some(-F::one())]
            )?;
            limbs.push(l[4].clone());
        }
        Ok(Number { limbs: limbs.try_into().unwrap() })
    }

    pub fn mod_exp(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        base: &Number<F>,
        exp: &Number<F>,
        modulus: &Number<F>,
    ) -> Result <Number<F>, Error> {
        let mut limbs = vec![];
        
        self.decompose_limb(region, offset, &exp.limbs[2], &mut limbs, 40)?;    //256 - 216 = 40
        self.decompose_limb(region, offset, &exp.limbs[1], &mut limbs, 108)?;
        self.decompose_limb(region, offset, &exp.limbs[0], &mut limbs, 108)?; 
 

        let mut acc = self.assign_constant(region, offset, Number::from_bn(&BigUint::from(0 as u128)))?;
        let zero = acc.clone();
        for limb in limbs {
            // let v = self.select(region, offset, &limb, &zero, base)?;
            // acc = self.mod_mult(region, offset, &acc, &acc, modulus)?;
            // acc = self.mod_add(region, offset, &acc, &v)?;
        }
        
        /*
         * General routine for a^b mod n, by repeated modular multiplication:
         * 
         *  - set an accumulator 'acc' to 1.
         *  - set a register 'squared' = a.
         *  - using register m as 'muled'
         *  - decompose the exponent into bits.
         *  - loop over all bits of the exponent.
         *  entry
         *    | → ┐
         *    ↑   ↓ 0. take a copy of acc by setting acc_old <-- acc
         *    ↑   ↓ 1. set m = (acc * squared) mod n
         *    ↑   ↓ 2. if: exponent bit is 1 then set acc <-- m
         *    ↑   ↓        exponent bit is 0 then set acc <-- acc_old
         *    ↑   ↓ 3. set squared = (squared * squared) mod n
         *    └ ← ┘
         */

        //let mut acc = self.assign_constant(region, offset, Number::from_bn(&BigUint::from(1 as u128)))?;  //commented out to not conflict above.
        let mut squared = base.clone();
        let mut muled = self.assign_constant(region, offset, Number::from_bn(&BigUint::from(0 as u128)))?;

        let bn_exp: BigUint = ((field_to_bn(&exp.limbs[2].value)) << 216) 
            + ((field_to_bn(&exp.limbs[1].value)) << 108) 
            + field_to_bn(&exp.limbs[0].value);

        let exp_bits = bn_exp
            .to_bytes_le()
            .into_iter()
            .flat_map(|v| {
                (0..8)
                    .map(|i: u8| (v >> i) & 1u8 == 1u8)
                    .collect::<Vec<bool>>()
            })
            .collect::<Vec<bool>>();

        let exp_bits = exp_bits[0..(bn_exp.bits() as usize)].to_vec();

        for exp_bit in exp_bits.into_iter() {

            // Compute `acc * squared`.
            let muled = self.mod_mult(region, offset, &acc, &squared, &modulus)?;

            // If exp_bit = true, set acc <-- (acc * squared). o.w., set acc <-- acc_old.
            // square squared. using mod_mult()
            // todo() finish implementation.
        }


        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use num_bigint::BigUint;



    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use crate::utils::*;
    use rand::{thread_rng, Rng};
    use num_bigint::RandomBits;

    const LIMB_WIDTH: usize = 108;

    use super::{
        ModExpChip,
        ModExpConfig,
        Number,
        Limb,
    };

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig
    }

    impl Chip<Fr> for HelperChip {
        type Config = HelperChipConfig;
        type Loaded = ();

        fn config(&self) -> &Self::Config {
            &self.config
        }

        fn loaded(&self) -> &Self::Loaded {
            &()
        }
    }

    impl HelperChip {
        fn new(config: HelperChipConfig) -> Self {
            HelperChip{
                config,
            }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let limb= cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_base(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            base: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(base))
        }

        fn assign_modulus(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            modulus: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(modulus))
        }

        fn assign_results(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            result: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            let n = Number::from_bn(result);
            let mut cells = vec![];
            for i in 0..4 {
                let c = region.assign_advice(
                    || format!("assign input"),
                    self.config.limb,
                    *offset + i,
                    || Ok(n.limbs[i].value)
                )?;
                cells.push(Some(c));
                *offset = *offset + 1;
            }
            let n = Number {
                limbs: [
                    Limb::new(cells[0].clone(), n.limbs[0].value),
                    Limb::new(cells[1].clone(), n.limbs[1].value),
                    Limb::new(cells[2].clone(), n.limbs[2].value),
                    Limb::new(cells[3].clone(), n.limbs[3].value),
                ]
            };
            Ok(n)
        }

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        base: BigUint,
        exp: BigUint,
        modulus: BigUint,
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        modexpconfig: ModExpConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            Self::Config {
               modexpconfig: ModExpChip::<Fr>::configure(meta),
               helperconfig: HelperChip::configure(meta)
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "assign mod exp",
                |mut region| {
                    let mut offset = 0;
                    let base = helperchip.assign_base(&mut region, &mut offset, &self.base)?;
                    let modulus = helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;

                    let exp = helperchip.assign_base(&mut region, &mut offset, &self.exp)?; 

                    let bn_res = self.base.clone() * self.exp.clone() % self.modulus.clone();   // needs pow

                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_res)?;

                    let rem = modexpchip.mod_exp(&mut region, &mut offset, &base, &exp, &modulus)?;
                    for i in 0..4 {
                        println!("rem is {:?}, result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                        println!("remcell is {:?}, resultcell is {:?}", &rem.limbs[i].cell, &result.limbs[i].cell);
                        region.constrain_equal(
                            rem.limbs[i].clone().cell.unwrap().cell(),
                            result.limbs[i].clone().cell.unwrap().cell()
                        )?;
                    }
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_modexp_circuit() {
        let base = BigUint::from(1u128 << 100);
        //let exp = BigUint::from(170u128);   // 0xAA
        //let exp = BigUint::parse_bytes(b"CBA9", 16).unwrap();
        //let exp = BigUint::parse_bytes(b"87", 16).unwrap();

        // let exp = BigUint::parse_bytes(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA", 16).unwrap() 
        //     + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108))
        //     + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108))
        //     + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108));   

        let exp = BigUint::parse_bytes(b"1B0000000000000000000000001CF0000000000000000000000003", 16).unwrap() 
            + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108))
            + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108))
            + (BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108));   
        
        

        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }





    #[test]
    fn test_mod_power108m1_circuit() {

        #[derive(Clone, Debug, Default)]
        struct TestModpower108m1Circuit {
            a: BigUint,
        }
    
        impl Circuit<Fr> for TestModpower108m1Circuit {
            type Config = TestConfig;
            type FloorPlanner = SimpleFloorPlanner;
    
            fn without_witnesses(&self) -> Self {
                Self::default()
            }
    
            fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
                Self::Config {
                   modexpconfig: ModExpChip::<Fr>::configure(meta),
                   helperconfig: HelperChip::configure(meta)
                }
            }
    
            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fr>,
            ) -> Result<(), Error> {
                let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
                let helperchip = HelperChip::new(config.clone().helperconfig);
     
                layouter.assign_region(
                    || "mod_power108m1",
                    |mut region| {
                        let mut offset = 0;
                        let a = helperchip.assign_base(&mut region, &mut offset, &self.a)?;
     
                        // calculate addition of all limbs.
                        let bn_lm0 = &self.a & (BigUint::from(1u128 << 108) - BigUint::from(1u128));
                        let bn_lm1 = BigUint::from(&self.a >> 108) & (BigUint::from(1u128 << 108) - BigUint::from(1u128));
                        let bn_lm2 = BigUint::from(&self.a >> 216) & (BigUint::from(1u128 << 108) - BigUint::from(1u128));
                        let bn_res = bn_lm0 + bn_lm1 + bn_lm2;
                        let result = helperchip.assign_results(&mut region, &mut offset, &bn_res)?;
    
                        let rem = modexpchip.mod_power108m1(&mut region, &mut offset, &a )?;

                        assert_eq!(field_to_bn(&rem[3].value), bn_res);
                        Ok(rem)
                    }
                )?;
    
                Ok(())
            }
        }

        // mod_power108m1() calculates a  (2^{108}-1) exactly for values a \in {0, (2^{108}-1)\}. 
        // for values greater than (2^{108}-1), mod_power108m1() overflows the 109+th bit.

        // test expected overflow of 1 bit 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff
        let a = BigUint::parse_bytes(b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", 16).unwrap() 
            * BigUint::parse_bytes(b"2", 16).unwrap() + BigUint::parse_bytes(b"1", 16).unwrap();  
        let test_circuit = TestModpower108m1Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));

        // test mathematical result for value < 108 bits, 0x1ffffffffffffffffffffffffffd
        let a = BigUint::parse_bytes(b"ffffffffffffffffffffffffffe", 16).unwrap() 
            * BigUint::parse_bytes(b"2", 16).unwrap() + BigUint::parse_bytes(b"1", 16).unwrap(); 
        let test_circuit = TestModpower108m1Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));

        // test overflow max bits
        let mut rng = thread_rng();
        let bit_len = (LIMB_WIDTH + LIMB_WIDTH + 108) as u64;
        let mut b = BigUint::default();
        while b.bits() != bit_len {
            b = rng.sample(RandomBits::new(bit_len));
        }
        let a = b;
        println!("bit_len = {}", bit_len);
        println!("a = 0x{}", a.to_str_radix(16));

        let test_circuit = TestModpower108m1Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));
    }


    #[test]
    fn test_mod_power216_circuit() {

        #[derive(Clone, Debug, Default)]
        struct TestModpower216Circuit {
            a: BigUint,
        }
    
        impl Circuit<Fr> for TestModpower216Circuit {
            type Config = TestConfig;
            type FloorPlanner = SimpleFloorPlanner;
    
            fn without_witnesses(&self) -> Self {
                Self::default()
            }
    
            fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
                Self::Config {
                   modexpconfig: ModExpChip::<Fr>::configure(meta),
                   helperconfig: HelperChip::configure(meta)
                }
            }
    
            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fr>,
            ) -> Result<(), Error> {
                let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
                let helperchip = HelperChip::new(config.clone().helperconfig);
     
                layouter.assign_region(
                    || "mod_power216",
                    |mut region| {
                        let mut offset = 0;
                        let base = helperchip.assign_base(&mut region, &mut offset, &self.a)?;
                        let bn_modulus = BigUint::from(1u128 << 108) * BigUint::from(1u128 << 108);
                        let modulus = helperchip.assign_modulus(&mut region, &mut offset, &bn_modulus)?;
                        let bn_rem = self.a.clone() % bn_modulus;
                        let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                        let rem = modexpchip.mod_power216(&mut region, &mut offset, &base )?;

                        for i in 0..4 {
                            println!("result is {:?}", &result.limbs[i].value);
                            println!("resultcell is {:?}", &result.limbs[i].cell);
                        }

                        // rem from mod_power216() should be equal to the bn calculated remainder.
                        assert_eq!(field_to_bn(&rem.value), bn_rem);
                        Ok(rem)
                    }
                )?;
    
                Ok(())
            }
        }
        // test should result in (2^216)-1) as rem
        let a = BigUint::parse_bytes(b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", 16).unwrap() 
            * BigUint::parse_bytes(b"2", 16).unwrap() + BigUint::parse_bytes(b"1", 16).unwrap();  
        let test_circuit = TestModpower216Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));

        let mut rng = thread_rng();
        let bit_len = (3*LIMB_WIDTH + 1) as u64;
        let mut b = BigUint::default();
        while b.bits() != bit_len {
            b = rng.sample(RandomBits::new(bit_len));
        }
        let a = b;
        println!("bit_len = {}", bit_len);
        println!("a = 0x{}", a.to_str_radix(16));

        let test_circuit = TestModpower216Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));


    }

    #[test]
    fn test_mod_mult_circuit() {

        #[derive(Clone, Debug, Default)]
        struct TestModMultCircuit {
            l: BigUint,
            r: BigUint,
            modulus: BigUint,
        }
    
        impl Circuit<Fr> for TestModMultCircuit {
            type Config = TestConfig;
            type FloorPlanner = SimpleFloorPlanner;
    
            fn without_witnesses(&self) -> Self {
                Self::default()
            }
    
            fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
                Self::Config {
                   modexpconfig: ModExpChip::<Fr>::configure(meta),
                   helperconfig: HelperChip::configure(meta)
                }
            }
    
            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fr>,
            ) -> Result<(), Error> {
                let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
                let helperchip = HelperChip::new(config.clone().helperconfig);
                layouter.assign_region(
                    || "assign mod mult",
                    |mut region| {
                        let mut offset = 0;
                        let base = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                        let modulus = helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                        let bn_rem = self.l.clone() * self.r.clone() % self.modulus.clone();

                        println!("bn_rem = 0x{}", bn_rem.to_str_radix(16));

                        let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                        let rem = modexpchip.mod_mult(&mut region, &mut offset, &base, &base, &modulus)?;
                        for i in 0..4 {
                            println!("rem is {:?}, result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                            println!("remcell is {:?}, resultcell is {:?}", &rem.limbs[i].cell, &result.limbs[i].cell);
                            region.constrain_equal(
                                rem.limbs[i].clone().cell.unwrap().cell(),
                                result.limbs[i].clone().cell.unwrap().cell()
                            )?;
                        }
                        Ok(())
                    }
                )?;
                Ok(())
            }
        }

        // test mod_mult() with l*l (mod modulus)
        let l = BigUint::from(3u128);
        let r = l.clone();
        let modulus = BigUint::from(5u128);

        let test_circuit = TestModMultCircuit{l, r, modulus} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e)
        };
        assert_eq!(prover.verify(), Ok(()));

    }











}


