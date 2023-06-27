
use crate::utils::{
    field_to_bn,
    bn_to_field,
};

use crate::circuits::{
    CommonGateConfig,
    Limb,
};

use crate::circuits::range::{
    RangeCheckConfig,
    RangeCheckChip,
};

use std::ops::{Mul, Div};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{
        //Chip, Region
        *,
    },
    plonk::{
        //ConstraintSystem, Error
        *,
    },
};
use std::marker::PhantomData;
use num_bigint::BigUint;

pub struct ModExpChip<F:FieldExt> {
    config: CommonGateConfig,
    _marker: PhantomData<F>
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
    type Config = CommonGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ModExpChip<F> {
    pub fn new(config: CommonGateConfig) -> Self {
        ModExpChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>, range_check_config: &RangeCheckConfig) -> CommonGateConfig {
        CommonGateConfig::configure(cs, range_check_config)
    }

    pub fn assign_constant (
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: Number<F>,
        limbbound: usize,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.assign_line(region, range_check_chip, offset,
                [
                    Some(number.limbs[i].clone()),
                    None,
                    None,
                    None,
                    None,
                    None,
                ],
                [Some(F::one()), None, None, None, None, None, None, None, Some(-F::from(number.limbs[i].value))],
                limbbound
            )?;
            limbs.push(l[0].clone())
        }
        Ok(Number {limbs: limbs.try_into().unwrap()})
    }


    pub fn assign_number (
        &self,
        _region: &mut Region<F>,
        _range_check_chip: &mut RangeCheckChip<F>,
        _offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        Ok(number)
    }

    pub fn mod_add (
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let ret = lhs.add(rhs);
        let limbs = ret.limbs.to_vec().into_iter().enumerate().map(|(i, l)| {
            let l = self.config.assign_line(
                region, range_check_chip, offset,
                [Some(lhs.limbs[i].clone()), Some(rhs.limbs[i].clone()), None, None, Some(l), None],
                [Some(F::one()), Some(F::one()), None, None, Some(F::one()), None, None, None, None],
                0,
            ).unwrap();
            l[2].clone() // the second is the sum result d
        }).collect::<Vec<_>>();
        Ok(Number {limbs: limbs.try_into().unwrap()})
    }

    pub fn mod_native_mul(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        rem: &Number<F>,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset, [
                None,
                Some(lhs.limbs[3].clone()), // lhs mod r
                Some(rhs.limbs[3].clone()), // rhs mod r
                Some(rem.limbs[3].clone()), // rem mod r
                None,
                None,
            ],
            [None, None, None, Some(-F::one()), None, None, None, None, Some(F::one())],
            0,
        )?;
        Ok(l[2].clone())
    }


    pub fn mod_power108m1 (
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: &Number<F>,
    ) -> Result<[Limb<F>; 4], Error> {
        let value = number.limbs[0].value + number.limbs[1].value + number.limbs[2].value; // 110 bits
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                Some(number.limbs[2].clone()),
                None,
                Some(Limb::new(None, value)),
                None
            ],
            [Some(F::one()), Some(F::one()), Some(F::one()), None, Some(-F::one()), None, None, None, None],
            0, //unchecked
        )?;
        Ok(l.try_into().unwrap())
    }

    pub fn mod_power216 (
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       number: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let value = number.limbs[0].value + number.limbs[1].value * (F::from_u128(1u128 << 108)); // 216 bits
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(number.limbs[0].clone()),
                Some(number.limbs[1].clone()),
                None,
                None,
                Some(Limb::new(None, value)),
                None
            ],
            [Some(F::one()), Some(F::from_u128(1u128 << 108)), None, None, Some(-F::one()), None, None, None, None],
            0,
        )?;
        Ok(l[2].clone())
    }


    pub fn mod_power108m1_mul (
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let bn_modulus = BigUint::from((1u128<<108)-1);
        let [_, _, _, ml] = self.mod_power108m1(region, range_check_chip, offset, lhs)?; // ml has at most 110 bits
        let [_, _, _, mr] = self.mod_power108m1(region, range_check_chip, offset, rhs)?; // mr has at most 110 bits
        let v = ml.value * mr.value; // at most 220 bits
        let bn_q = field_to_bn(&v).div(bn_modulus.clone()); // at most 112 bits
        let bn_r = field_to_bn(&v) - bn_q.clone() * bn_modulus; // at most 108 bits
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [Some(q), Some(ml), Some(mr), Some(r), None, None],
            [Some(F::from_u128((1u128<<108)-1)), None, None, Some(F::one()), None, None, None, Some(-F::one()), None],
            10,
        )?;
        Ok(l[3].clone())
    }

    pub fn mod_power216_mul (
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let x0 = lhs.limbs[0].value;
        let x1 = lhs.limbs[1].value;
        let y0 = rhs.limbs[0].value;
        let y1 = rhs.limbs[1].value;

        let mut v =  x0 * y1 + x1 * y0; // 217 bits
        let l = self.config.assign_line(
            region,
            range_check_chip,
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
            0
        )?;
        let vcell = l[4].clone(); // 217 bits

        //  compute v mod 2^108
        let bn_q = field_to_bn(&v).div(BigUint::from(1u128<<108)); // bn_q is 109 bits
        let bn_r = field_to_bn(&v) - bn_q.clone() * BigUint::from(1u128 << 108); // 108 bits
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [Some(q), Some(vcell), None, Some(r), None, None],
            [Some(F::from_u128(1u128<<108)), Some(-F::one()), None, Some(F::one()), None, None, None, None, None],
            10,
        )?;

        let rcell = l[2].clone(); // 108 bits unchecked

        v = rcell.value * F::from_u128(1u128<<108) + x0 * y0; // 217 bits

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(lhs.limbs[0].clone()),
                Some(rcell),
                None,
                Some(rhs.limbs[0].clone()),
                Some(Limb::new(None, v)),
                None
            ],
            [None, Some(F::from_u128(1u128<<108)), None, None, Some(-F::one()), None, Some(F::one()), None, None],
            10 // TODO: need to check rcell range
        )?;
        range_check_chip.assign_value_with_range(region, l[1].clone().value, 9)?;
        

        Ok(l[3].clone()) // 217 bits
    }

    pub fn mod_power108m1_zero(
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        let c = (1u128<<108)-1; // 108 bits
        let v = F::from_u128(c * 16u128) + limbs[0].value*signs[0] + limbs[1].value *signs[1] + limbs[2].value*signs[2]; // 220 bits
        let q = field_to_bn(&v).div(c); // 112 bits
        self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(Limb::new(None, bn_to_field(&q))),
                Some(limbs[0].clone()),
                Some(limbs[1].clone()),
                Some(limbs[2].clone()),
                None,
                None
            ],
            [Some(-F::from_u128(c)), Some(signs[0]), Some(signs[1]), Some(signs[2]), None, None, None, None, Some(F::from_u128(c*16u128))],
            10 // check rcell range

        )?;
        Ok(())
    }

    pub fn mod_power216_zero(
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        //let c = field_to_bn(&F::from_u128(1u128<<108)).mul(BigUint::from(1u128<<108)); // 216 bits  
        //let v = bn_to_field(&(c.mul(BigUint::from(2u128)))) + limbs[0].value*signs[0] + limbs[1].value *signs[1] + limbs[2].value*signs[2];
         
        let c = F::from_u128(1u128<<108) * F::from_u128(1u128<<109); // 217 bits    
        let v = c * F::from_u128(2u128) + limbs[0].value*signs[0] + limbs[1].value *signs[1] + limbs[2].value*signs[2]; // 218 bits
        let q = field_to_bn(&v).div(field_to_bn(&c));
        self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(Limb::new(None, bn_to_field(&q))),
                Some(limbs[0].clone()),
                Some(limbs[1].clone()),
                Some(limbs[2].clone()),
                None,
                None
            ],
            [Some(-c), Some(signs[0]), Some(signs[1]), Some(signs[2]), None, None, None, None, Some(c*F::from_u128(2u128))],
            1 // check rcell range
        )?;
       
        Ok(())
        
    }

    pub fn mod_mult(
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       lhs: &Number<F>,
       rhs: &Number<F>,
       modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        /*
         * x0,x1,x2 * y0,y1,y2 = q0,q1,q2 * m0,m1,m2 + r0,r1,r2
         * mod 2^{108}-1:
         *     (x2+x1+x0)*(y0+y1+y2) = (q0+q1+q2)*(m0+m1+m2)+(r0+r1+r2)
         * mod 2^{216}:
         *     (x1*y0+x0*y1)*2^108+x0*y0 = (q0*m1+q1*m0)*2^{108}+q0*m0+r1+r0
         *      (108 * 108 + 108 * 108) * 2^108 + 108 * 108 = (108 * 108 + 108 * 108) * 2^216 + 108 * 108 + 108 + 108
         *      (216 + 216 = 217) * 216 + 216 = (216 + 216 = 217) * 216 + 216 + 108 + 108
         *      (433) = (217 * 216) + 216 + 108 + 108
         * native:
         *    x*y = q*m + r
         */
        let bn_lhs = lhs.to_bn(); // 256 bits
        let bn_rhs = rhs.to_bn(); // 256 bits
        let bn_mult = bn_lhs.mul(bn_rhs); // 512 bits
        let bn_modulus = modulus.to_bn(); // 254 bits
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone()); // 512 - 254 = 258 bits
        let bn_rem = bn_mult - (bn_quotient.clone() * bn_modulus.clone()); // 258 bits
        let modulus = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_modulus))?;
        let rem = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_rem))?;
        let quotient = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_quotient))?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, range_check_chip, offset, lhs, rhs)?; // 220 bits
        let mod_108m1_rhs = self.mod_power108m1_mul(region, range_check_chip, offset, &quotient, &modulus)?; // 220 bits
        let [r0, r1, r2, mod_108m1_rem] = self.mod_power108m1(region, range_check_chip, offset, &rem)?; // 110 bits
        self.mod_power108m1_zero( 
            region,
            range_check_chip,
            offset,
            vec![mod_108m1_lhs.clone(), mod_108m1_rhs.clone(), mod_108m1_rem.clone()],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, range_check_chip, offset, lhs, rhs)?; //217 bits
        let mod_216_rhs = self.mod_power216_mul(region, range_check_chip, offset, &quotient, &modulus)?; //217 bits
        let mod_216_rem = self.mod_power216(region, range_check_chip, offset, &rem)?; //216 bits
        self.mod_power216_zero(
            region,
            range_check_chip,
            offset,
            vec![mod_216_lhs, mod_216_rhs, mod_216_rem],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_native = self.mod_native_mul(
            region,
            range_check_chip,
            offset,
            &rem,
            &lhs,
            &rhs,
        )?;
        Ok(Number {
            limbs: [r0, r1, r2, mod_native]
        })
    }

    pub fn select(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        cond: &Limb<F>,
        one: &Number<F>,
        base: &Number<F>,
    ) -> Result <Number<F>, Error> {
        //c * base + (1-c) * one
        let result = if cond.value == F::zero() {one.clone()} else {base.clone()};
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.assign_line(region, range_check_chip, offset,
                [
                    Some(base.limbs[i].clone()),
                    Some(one.limbs[i].clone()),
                    Some(cond.clone()),
                    Some(cond.clone()),
                    Some(result.limbs[i].clone()),
                    None,
                ],
                [None, Some(F::one()), None, None, Some(-F::one()), None, Some(F::one()), Some(-F::one()), None],
                0,
            )?;
            limbs.push(l[4].clone());
        }
        Ok(Number { limbs: limbs.try_into().unwrap() })
    }

    pub fn mod_exp(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        base: &Number<F>,
        exp: &Number<F>,
        modulus: &Number<F>,
    ) -> Result <Number<F>, Error> {
        assert!(modulus.to_bn() > BigUint::from(0u128));

        let mut limbs = vec![];
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[2], &mut limbs, 40)?; //256 - 216 = 40
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[1], &mut limbs, 108)?;
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[0], &mut limbs, 108)?;
        let mut acc = self.assign_constant(region, range_check_chip, offset, Number::from_bn(&BigUint::from(1 as u128)), 0)?;
        let one = acc.clone();
        for limb in limbs {
            let v = self.select(region, range_check_chip, offset, &limb, &one, base)?;
            acc = self.mod_mult(region, range_check_chip, offset, &acc, &acc, modulus)?;
            acc = self.mod_mult(region, range_check_chip, offset, &acc, &v, modulus)?;
        }
        
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use num_bigint::BigUint;
    use crate::circuits::range::{
        RangeCheckConfig,
        RangeCheckChip,
    };
    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        ModExpChip,
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

        fn assign_exp(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            exp: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(exp))
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
                    || value_for_assign!(n.limbs[i].value)
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
        modexpconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
               modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
               helperconfig: HelperChip::configure(meta),
               rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "assign mod mult",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let base = helperchip.assign_base(&mut region, &mut offset, &self.base)?;
                    let exp = helperchip.assign_exp(&mut region, &mut offset, &self.exp)?;
                    let modulus = helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                    let bn_rem = self.base.clone().modpow(&self.exp, &self.modulus);
                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                    let rem = modexpchip.mod_exp(&mut region, &mut range_chip, &mut offset, &base, &exp, &modulus)?;
                    for i in 0..4 {
                        //println!("rem is {:?}, result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                        //println!("rem cell is {:?}, result cell is {:?}", &rem.limbs[i].cell, &result.limbs[i].cell);
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
    fn test_modexp_circuit_00() {
        let base = BigUint::from(1u128 << 100);
        let exp = BigUint::from(2u128 << 100);
        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_modexp_circuit_01() {
        let base = BigUint::from(1u128);
        let exp = BigUint::from(2u128);
        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    #[test]
    fn test_modexp_circuit_02() {
        let base = BigUint::from(2u128);
        let exp = BigUint::from(2u128);
        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_modexp_circuit_03() {
        let base = BigUint::from(5u128);
        let exp = BigUint::from(1u128 << 108);
        let modulus = BigUint::from(0u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    //panicked at 'attempt to calculate with zero modulus!'

    #[test]
    fn test_modexp_circuit_04() {
        let base = BigUint::from(5u128);
        let exp = BigUint::from(1u128 << 108);
        let modulus = BigUint::from(128u128 << 127); //128 = 2^7 out of range of u128
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    //panicked at 'attempt to calculate with zero modulus!'

    #[test]
    fn test_modexp_circuit_05() {
        let base = BigUint::from(5u128);
        let exp = BigUint::from(128u128 << 108);
        let modulus = BigUint::from(1u128 << 100) * BigUint::from(1u128 << 100);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
    //panicked at 'assertion failed: ws[0] * cs[0] + ws[1] * cs[1] + ws[2] * cs[2] + ws[3] * cs[3] + ws[4] * cs[4]\n                    + ws[5] * cs[5] + ws[0] * ws[3] * cs[6] +\n            ws[1] * ws[2] * cs[7] + cs[8] == F::zero()', src/circuits/mod.rs:263:9

    #[test]
    fn test_modexp_circuit_06() {
        let base = BigUint::from(5u128);
        let exp = BigUint::from(1u128 << 108);
        let modulus = BigUint::from(128u128 << 117); 
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
        //prover.assert_satisfied();
        
    }
    //panicked at 'assertion failed: 
}

