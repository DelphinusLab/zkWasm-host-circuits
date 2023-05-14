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
    circuit::{Chip, Layouter, Region, AssignedCell},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use std::ops::{Shr, Shl};
use crate::constant;
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


    pub fn assign_add (
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

    pub fn mod_power108m1 (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
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
        Ok(l[3].clone())
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
        let ml = self.mod_power108m1(region, offset, lhs)?;
        let mr = self.mod_power108m1(region, offset, rhs)?;
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

    pub fn assign_mod_mult(
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
        let mod_108m1_rem = self.mod_power108m1(region, offset, &rem)?;
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
            vec![mod_108m1_lhs, mod_108m1_rhs, mod_108m1_rem],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        Ok(rem)
    }


    pub fn square_mod(
       &self,
       region: &mut Region<F>,
       offset: &mut usize,
       square: &Number<F>,
       divisor: &Number<F>
    ) -> Result <Number<F>, Error> {
        // result = ???
        // square * square = k * divisor + result
        //let mod_128;
        //Ok(result)
        todo!();
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use num_bigint::BigUint;

    use halo2_proofs::{
        circuit::{Cell, Chip, Layouter, Region, AssignedCell, SimpleFloorPlanner},
        plonk::{
            Fixed, Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Instance,
            Selector,
        },
    };

    use super::{
        ModExpChip,
        ModExpConfig,
        Number,
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
            layouter: &mut impl Layouter<Fr>,
            offset: &mut usize,
            base: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(base))
        }

        fn assign_modulus(
            &self,
            layouter: &mut impl Layouter<Fr>,
            offset: &mut usize,
            modulus: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(modulus))
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
            let mut offset = 0;
            let base = helperchip.assign_base(&mut layouter, &mut offset, &self.base)?;
            let modulus = helperchip.assign_modulus(&mut layouter, &mut offset, &self.modulus)?;

            let rem = layouter.assign_region(
                || "assign mod mult",
                |mut region| {
                    let rem = modexpchip.assign_mod_mult(&mut region, &mut offset, &base, &base, &modulus)?;
                    println!("result is {:?}", rem);
                    Ok(rem)
                }
            )?;

            Ok(())
        }
    }


    #[test]
    fn test_modexp_circuit() {
        let base = BigUint::from(1u128 << 100);
        let exp = BigUint::from(2u128 << 100);
        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}


