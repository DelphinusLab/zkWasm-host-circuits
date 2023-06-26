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
    circuit::{Chip, Region},
    plonk::{
        ConstraintSystem, Error
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
                [None, None, None, None, None, None, Some(F::from(number.limbs[i].value)), None, None],
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
            l[2].clone() // the fifth is the sum result d
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
                Some(lhs.limbs[3].clone()),
                Some(rhs.limbs[3].clone()),
                Some(rem.limbs[3].clone()),
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
        let value = number.limbs[0].value + number.limbs[1].value + number.limbs[2].value;
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
            0,
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
        let value = number.limbs[0].value + number.limbs[1].value * (F::from_u128(1u128 << 108));
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
        let [_, _, _, ml] = self.mod_power108m1(region, range_check_chip, offset, lhs)?; // ml has at most 109 bits
        let [_, _, _, mr] = self.mod_power108m1(region, range_check_chip, offset, rhs)?; // mr has at most 109 bits
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

        let mut v =  x0 * y1 + x1 * y0; // 219 bits
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
        let vcell = l[4].clone(); // 219 bits

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

        v = rcell.value * F::from_u128(1u128<<108) + x0 + y0;

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
            [Some(F::one()), Some(F::from_u128(1u128<<108)), None, Some(F::one()), Some(-F::one()), None, None, None, None],
            0 // TODO: need to check rcell range
        )?;

        Ok(l[3].clone())
    }

    pub fn mod_power108m1_zero(
       &self,
       region: &mut Region<F>,
       range_check_chip: &mut RangeCheckChip<F>,
       offset: &mut usize,
       limbs: Vec<Limb<F>>,
       signs: Vec<F>,
    ) -> Result<(), Error> {
        let c = (1u128<<108)-1;
        let v = F::from_u128(c * 16u128) + limbs[0].value*signs[0] + limbs[1].value *signs[1] + limbs[2].value*signs[2];
        let q = field_to_bn(&v).div(c);
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
            1 // check rcell range
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
        //todo!()
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
         *     (x1*y0+x0*y1)*2^216+x0*y0 = (q0*m1+q1*m0)*2^{216}+q0*m0+r1+r0
         * native:
         *    x*y = q*m + r
         */
        let bn_lhs = lhs.to_bn();
        let bn_rhs = rhs.to_bn();
        let bn_mult = bn_lhs.mul(bn_rhs);
        let bn_modulus = modulus.to_bn();
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone()); //div_rem
        let bn_rem = bn_mult - (bn_quotient.clone() * bn_modulus.clone());
        let modulus = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_modulus))?;
        let rem = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_rem))?;
        let quotient = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_quotient))?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_108m1_rhs = self.mod_power108m1_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let [r0, r1, r2, mod_108m1_rem] = self.mod_power108m1(region, range_check_chip, offset, &rem)?;
        self.mod_power108m1_zero(
            region,
            range_check_chip,
            offset,
            vec![mod_108m1_lhs.clone(), mod_108m1_rhs.clone(), mod_108m1_rem.clone()],
            vec![F::one(), -F::one(), -F::one()]
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_216_rhs = self.mod_power216_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let mod_216_rem = self.mod_power216(region, range_check_chip, offset, &rem)?;

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

    /// Selects result based on the condition exp_bit = '1' or '0' \
    /// 
    /// # Arguments 
    /// 
    /// * `cond` - the exp_bit as a Limb in F, is only 0x1 or 0x0
    /// * `base` - the value of the base as a Number<F>
    /// * `one`  - the value of 1 as a Number<F>
    /// 
    /// # Constraint 
    /// 
    ///     (w[1] * w[2] * c[7]) + (w[0] * w[3] * c[6]) + (w[4] * c[4]) + (w[3] * c[3]) = 0
    ///     (cond * base * 1   ) + (cond * base * -1  ) + (res * 1    ) + (one * -1   ) = 0
    /// 
    /// where: \
    ///         res = base,   if exp_bit = '1' \
    ///         res = one,    if exp_bit = '0' \
    /// 
    /// # Example
    /// ```
    /// let select(region, offset, &cond, &base, &one);
    /// ```
    /// 
    pub fn select(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        cond: &Limb<F>,
        base: &Number<F>,
        one: &Number<F>,
    ) -> Result <Number<F>, Error> {
        let w4_val = if cond.value == F::one() { base.clone() } else { one.clone() };
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.assign_line(region, range_check_chip, offset,
                [
                    Some(cond.clone()),
                    Some(cond.clone()),
                    Some(base.limbs[i].clone()),    
                    Some(one.limbs[i].clone()),     
                    Some(w4_val.limbs[i].clone()),  
                    None,
                ],
                [
                    None, None, None, Some(-F::one()), Some(F::one()), 
                    None, Some(F::one()), Some(-F::one()), None
                ],
                0 // check this value is correct for select
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
        let mut limbs = vec![];
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[2], &mut limbs, 40)?; //256 - 216 = 40
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[1], &mut limbs, 108)?;
        self.config.decompose_limb(region, range_check_chip, offset, &exp.limbs[0], &mut limbs, 108)?;
        let mut acc = self.assign_constant(region, range_check_chip, offset, Number::from_bn(&BigUint::from(1 as u128)), 0)?;
        let one = acc.clone();
        for limb in limbs.iter() {
            acc = self.mod_mult(region, range_check_chip, offset, &acc, &acc, modulus)?;
            let sval = self.select(region, range_check_chip, offset, &limb, &base, &one)?;
            acc = self.mod_mult(region, range_check_chip, offset, &acc, &sval, modulus)?;
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
}



#[cfg(test)]
mod tests_2 {
    use halo2_proofs::{pairing::bn256::Fr, arithmetic::FieldExt};
    use halo2_proofs::dev::MockProver;
    use num_bigint::{BigUint, ToBigInt, ToBigUint};

    use crate::circuits::range::{
        RangeCheckConfig,
        RangeCheckChip,
    };
    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;

    use halo2_proofs::{
        circuit::{Cell, Chip, Layouter, Region, AssignedCell, SimpleFloorPlanner},
        plonk::{
            Fixed, Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Expression, Instance,
            Selector,
        },
    };

    use rand::{thread_rng, Rng};
    use num_bigint::RandomBits;
    const LIMB_WIDTH: usize = 108;

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

        fn assign_modulus(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            modulus: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(modulus))
        }

        fn assign_exp(
            &self,
            _region: &mut Region<Fr>,
            _offset: &mut usize,
            exponent: &BigUint,
        ) -> Result<Number<Fr>, Error> {
            Ok(Number::from_bn(exponent))
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

    //------------------------------------------------------------
    use std::fmt;
    use halo2_proofs::{
        dev::{
            VerifyFailure, 
            FailureLocation,
        },
        plonk::Any,
    };
    
    pub enum CircuitError {
        /// Thrown when `MockProver::run` fails to prove the circuit.
        ProverError(Error),
        /// Thrown when verification fails.
        VerifierError(Vec<VerifyFailure>),
        /// Thrown when no operation has been specified.
        NoOperation,
    }
    
    impl fmt::Debug for CircuitError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                CircuitError::ProverError(prover_error) => {
                    write!(f, "prover error in circuit: {}", prover_error)
                }
                CircuitError::VerifierError(verifier_error) => {
                    write!(f, "verifier error in circuit: {:#?}", verifier_error)
                }
                CircuitError::NoOperation => {
                    write!(f, "no operation is set (this should never happen.")
                }
            }
        }
    }
    //------------------------------------------------------------

    #[derive(Clone, Debug, Default)]
    struct TestDecomposeLimbCircuit {
        l: BigUint,
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        modexpconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }


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
                || "mod_power108m1",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let bn_rem = self.a.clone()  % (BigUint::from(1u128 << 108) - BigUint::from(1u128));
                    let a = helperchip.assign_base(&mut region, &mut offset, &self.a)?;
                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                    let rem = modexpchip.mod_power108m1(&mut region, &mut range_chip, &mut offset, &a )?;
                    println!("bn_res = 0x{}", bn_rem.to_str_radix(16));
                    println!("\nrem is (hex):");
                    for i in 0..4 {
                        println!("rem[{i}] = {:?}", &rem[i].value);
                    }
                    for i in 0..4 {
                        println!("result is {:?}", &result.limbs[i].value);
                        println!("resultcell is {:?}", &result.limbs[i].cell);
                        // region.constrain_equal(
                        //     rem.limbs[i].clone().cell.unwrap().cell(),
                        //     result.limbs[i].clone().cell.unwrap().cell()
                        // )?;
                    }
                    Ok(rem)
                }
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModpower108m1mulCircuit {
        a: BigUint,
        b: BigUint,
        modulus: BigUint,
    }

    impl Circuit<Fr> for TestModpower108m1mulCircuit {
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
                || "mod_power108m1_mul",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let bn_rem = self.a.clone() * self.b.clone() % self.modulus.clone();
                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                    let lhs  = helperchip.assign_modulus(&mut region, &mut offset, &self.a)?;
                    let rhs  = helperchip.assign_base(&mut region, &mut offset, &self.b)?;
                    let res = modexpchip.mod_power108m1_mul(&mut region, &mut range_chip,&mut offset, &lhs, &rhs )?;     
                    println!("\nbn_rem    = {:?}", bn_rem);
                    println!("result is = {:?}", res.value);
                    Ok(res)
                }
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModPower216MulCircuit {
        l: BigUint,
        r: BigUint,
        modulus: BigUint,
    }

    impl Circuit<Fr> for TestModPower216MulCircuit {
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
                || "test circuit mod_power216_mul",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let bn_rem = self.l.clone() * self.r.clone() % self.modulus.clone();
                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                    let lhs  = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                    let rhs  = helperchip.assign_base(&mut region, &mut offset, &self.r)?;
                    let res = modexpchip.mod_power216_mul(&mut region, &mut range_chip,&mut offset, &lhs, &rhs)?;     
                    println!("\nbn_rem \t= {}", bn_rem.to_str_radix(16));
                    println!("res \t= {:?}", res.value);
                    Ok(res)
                }
            )?;
            Ok(())
        }
    }


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
                || "test circuit mod_mult",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let bn_rem = self.l.clone() * self.r.clone() % self.modulus.clone();
                    let result = helperchip.assign_results(&mut region, &mut offset, &bn_rem)?;
                    let modulus  = helperchip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                    let lhs  = helperchip.assign_base(&mut region, &mut offset, &self.l)?;
                    let rhs  = helperchip.assign_base(&mut region, &mut offset, &self.r)?;
                    let res = modexpchip.mod_mult(&mut region, &mut range_chip,&mut offset, &lhs, &rhs, &modulus)?;     
                    println!("\nbn_rem    = {:?}", bn_rem);
                    for i in 0..4 {
                        println!("res = {:?}", &res.limbs[i].value);
                    }
                    Ok(res)
                }
            )?;
            Ok(())
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestModExpCircuit {
        base: BigUint,
        exp: BigUint,
        modulus: BigUint,
    }

    impl Circuit<Fr> for TestModExpCircuit {
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
                || "assign mod exp",
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
                        println!("rem is {:?}, \t result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                        println!("remcell is \t{:?}", &rem.limbs[i].cell);
                        println!("resultcell is \t {:?}", &result.limbs[i].cell);
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

    fn run_mod_power108m1_circuit() -> Result<(), CircuitError> {
        // test mod_power108m1 for over x bits
        let mut rng = thread_rng();
        let bit_len = (LIMB_WIDTH + LIMB_WIDTH + 108) as u64;
        let mut b = BigUint::default();
        while b.bits() != bit_len {
            b = rng.sample(RandomBits::new(bit_len));
        }
        let a = b;
        println!("bit_len = {}", bit_len);
        println!("a = 0x{}", a.to_str_radix(16));

        let a = BigUint::parse_bytes(b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", 16).unwrap() 
            * BigUint::parse_bytes(b"2", 16).unwrap() + BigUint::parse_bytes(b"1", 16).unwrap();  
        // test expected overflow of 1 bit 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff

        let test_circuit = TestModpower108m1Circuit{a} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        //assert_eq!(prover.verify(), Ok(()));
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        Ok(())
    }

    fn run_mod_power108m1_mul_circuit() -> Result<(), CircuitError> {

        let a = BigUint::parse_bytes(b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", 16).unwrap() 
            * BigUint::parse_bytes(b"2", 16).unwrap() + BigUint::parse_bytes(b"1", 16).unwrap();  
        // test expected overflow of 1 bit 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff
        let b = BigUint::from(1u128);
        let modulus = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
        let test_circuit = TestModpower108m1mulCircuit{a, b, modulus} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };
        Ok(())
    }

    fn run_mod_power216_mul_circuit() -> Result<(), CircuitError> {

        let l = BigUint::from(2454u128);
        let r = BigUint::from(1u128);
        let modulus = BigUint::from(1u128<<108) * BigUint::from(1u128<<108);
        let test_circuit = TestModPower216MulCircuit{l, r, modulus} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        let l = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
        let r = BigUint::from(1u128);
        let modulus = BigUint::from(1u128<<108) * BigUint::from(1u128<<108);
        let test_circuit = TestModPower216MulCircuit{l, r, modulus} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        Ok(())
    }

    fn run_mod_mult_circuit() -> Result<(), CircuitError> {

        let l = BigUint::from(2454u128);
        let r = BigUint::from(1u128);
        let modulus = BigUint::from(18u128);
        let test_circuit = TestModMultCircuit{l, r, modulus} ;
        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };
        Ok(())
    }

    fn run_modexp_circuit() -> Result<(), CircuitError> {

        let base = BigUint::from(5u128); 
        let exp = BigUint::from(22u128);
        let modulus = BigUint::from(37u128);
        let test_circuit = TestModExpCircuit {base, exp, modulus} ;

        let prover = match MockProver::run(16, &test_circuit, vec![]) {
            Ok(prover_run) => prover_run,
            Err(prover_error) => return Err(CircuitError::ProverError(prover_error)),
        };
    
        match prover.verify() {
            Ok(_) => (),
            Err(verifier_error) => return Err(CircuitError::VerifierError(verifier_error)),
        };

        Ok(())


    }




    #[test]
    fn test_mod_power108m1_only() {
        let output = run_mod_power108m1_circuit().expect("mod_power108m1_circuit failed prover verify");
        println!("proof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_power108m1_mul() {
        let output = run_mod_power108m1_mul_circuit().expect("mod_power108m1_mul failed prover verify");
        println!("proof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_power216_mul() {
        let output = run_mod_power216_mul_circuit().expect("run_mod_mult_circuit failed prover verify"); 
        println!("proof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_mod_mult() {
        let output = run_mod_mult_circuit().expect("run_mod_mult_circuit failed prover verify");
        println!("proof generation successful!\nresult: {:#?}", output);
    }

    #[test]
    fn test_modexp() {
        let output = run_modexp_circuit().expect("run_modexp_circuit failed prover verify");    //--> pass
        println!("proof generation successful!\nresult: {:#?}", output);
    }

}

