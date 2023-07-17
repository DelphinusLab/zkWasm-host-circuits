use crate::utils::{bn_to_field, field_to_bn, Limb};

use crate::circuits::CommonGateConfig;

use crate::circuits::range::{RangeCheckChip, RangeCheckConfig};

use std::ops::{Div, Mul};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region},
    plonk::{ConstraintSystem, Error},
};
use num_bigint::BigUint;
use std::marker::PhantomData;

pub struct ModExpChip<F: FieldExt> {
    config: CommonGateConfig,
    _marker: PhantomData<F>,
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
            ],
        }
    }
    fn from_bn(bn: &BigUint) -> Self {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb1 = (bn - limb0.clone())
            .div(BigUint::from(1u128 << 108))
            .modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb2 = bn
            .div(BigUint::from(1u128 << 108))
            .div(BigUint::from(1u128 << 108));
        let native = bn.div(field_to_bn(&(-F::one()))) + BigUint::from(1u128);
        Number {
            limbs: [
                Limb::new(None, bn_to_field(&limb0)),
                Limb::new(None, bn_to_field(&limb1)),
                Limb::new(None, bn_to_field(&limb2)),
                Limb::new(None, bn_to_field(&native)),
            ],
        }
    }
    fn to_bn(&self) -> BigUint {
        let limb0 = field_to_bn(&self.limbs[0].value);
        let limb1 = field_to_bn(&self.limbs[1].value);
        let limb2 = field_to_bn(&self.limbs[2].value);
        (limb2 * BigUint::from(1u128 << 108) + limb1) * BigUint::from(1u128 << 108) + limb0
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

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        range_check_config: &RangeCheckConfig,
    ) -> CommonGateConfig {
        CommonGateConfig::configure(cs, range_check_config)
    }

    fn assign_constant_number(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.assign_constant(
                region,
                range_check_chip,
                offset,
                &F::from(number.limbs[i].value),
            )?;
            limbs.push(l.clone())
        }
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    fn assign_number(
        &self,
        _region: &mut Region<F>,
        _range_check_chip: &mut RangeCheckChip<F>,
        _offset: &mut usize,
        number: Number<F>,
    ) -> Result<Number<F>, Error> {
        Ok(number)
    }

    pub fn mod_add(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let ret = lhs.add(rhs);
        let limbs = ret
            .limbs
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(i, l)| {
                let l = self
                    .config
                    .assign_line(
                        region,
                        range_check_chip,
                        offset,
                        [
                            Some(lhs.limbs[i].clone()),
                            Some(rhs.limbs[i].clone()),
                            None,
                            None,
                            Some(l),
                            None,
                        ],
                        [
                            Some(F::one()),
                            Some(F::one()),
                            None,
                            None,
                            Some(F::one()),
                            None,
                            None,
                            None,
                            None,
                        ],
                        0,
                    )
                    .unwrap();
                l[2].clone() // the fifth is the sum result d
            })
            .collect::<Vec<_>>();
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    fn mod_native_mul(
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
            offset,
            [
                None,
                Some(lhs.limbs[3].clone()),
                Some(rhs.limbs[3].clone()),
                Some(rem.limbs[3].clone()),
                None,
                None,
            ],
            [
                None,
                None,
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
                Some(F::one()),
            ],
            0,
        )?;
        Ok(l[2].clone())
    }

    fn mod_power108m1(
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
                None,
            ],
            [
                Some(F::one()),
                Some(F::one()),
                Some(F::one()),
                None,
                Some(-F::one()),
                None,
                None,
                None,
                None,
            ],
            0,
        )?;
        Ok(l.try_into().unwrap())
    }

    fn mod_power216(
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
                None,
            ],
            [
                Some(F::one()),
                Some(F::from_u128(1u128 << 108)),
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
        Ok(l[2].clone())
    }

    fn mod_power108m1_mul(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
    ) -> Result<Limb<F>, Error> {
        let bn_modulus = BigUint::from((1u128 << 108) - 1);
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
            [
                Some(F::from_u128((1u128 << 108) - 1)),
                None,
                None,
                Some(F::one()),
                None,
                None,
                None,
                Some(-F::one()),
                None,
            ],
            10,
        )?;
        Ok(l[3].clone())
    }

    ///
    /// # Apply constraint:
    /// (r     * 1    ) + (x0    * y0    * 1    ) + (v     * 1    ) = 0 \
    /// (ws[0] * cs[0]) + (ws[1] * ws[2] * cs[7]) + (ws[4] * cs[4]) = 0
    ///
    fn mod_power216_mul(
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
        let mut v = x0 * y1 + x1 * y0; //0-2^216
        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(lhs.limbs[0].clone()), //x0
                Some(lhs.limbs[1].clone()), //x1
                Some(rhs.limbs[0].clone()), //y0
                Some(rhs.limbs[1].clone()), //y1
                Some(Limb::new(None, v)),
                None,
            ],
            [
                None,
                None,
                None,
                None,
                Some(-F::one()),
                None,
                Some(F::one()),
                Some(F::one()),
                None,
            ],
            0,
        )?;
        let vcell = l[4].clone();

        //  compute v mod 2^108
        let bn_q = field_to_bn(&v).div(BigUint::from(1u128 << 108));
        let bn_r = field_to_bn(&v) - bn_q.clone() * BigUint::from(1u128 << 108);
        let q = Limb::new(None, bn_to_field(&bn_q));
        let r = Limb::new(None, bn_to_field(&bn_r));

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [Some(q), Some(vcell), None, Some(r), None, None],
            [
                Some(F::from_u128(1u128 << 108)),
                Some(-F::one()),
                None,
                Some(F::one()),
                None,
                None,
                None,
                None,
                None,
            ],
            10,
        )?;
        let rcell = l[2].clone();
        v = rcell.value * F::from_u128(1u128 << 108) + x0 * y0;

        let l = self.config.assign_line(
            region,
            range_check_chip,
            offset,
            [
                Some(rcell),
                Some(lhs.limbs[0].clone()),
                Some(rhs.limbs[0].clone()),
                None,
                Some(Limb::new(None, v)),
                None,
            ],
            [
                Some(F::from_u128(1u128 << 108)),
                None,
                None,
                None,
                Some(-F::one()),
                None,
                None,
                Some(F::one()),
                None,
            ],
            0, // TODO: need to check rcell range
        )?;
        Ok(l[3].clone())
    }

    fn mod_power108m1_zero(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        limbs: Vec<Limb<F>>,
        signs: Vec<F>,
    ) -> Result<(), Error> {
        let c = (1u128 << 108) - 1;
        let v = F::from_u128(c * 16u128)
            + limbs[0].value * signs[0]
            + limbs[1].value * signs[1]
            + limbs[2].value * signs[2];
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
                None,
            ],
            [
                Some(-F::from_u128(c)),
                Some(signs[0]),
                Some(signs[1]),
                Some(signs[2]),
                None,
                None,
                None,
                None,
                Some(F::from_u128(c * 16u128)),
            ],
            1, // check rcell range
        )?;
        Ok(())
    }

    ///
    /// # Apply constraint:
    /// (q * -c) + (sum(limb_i * sign_i)) + (c * BUFMULT)  = 0
    ///
    fn mod_power216_zero(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        limbs: Vec<Limb<F>>,
        signs: Vec<F>,
    ) -> Result<(), Error> {
        const BUFMULT: u128 = 2u128; // as long as its > 2-bits wide.
        let f_c = F::from_u128(1u128 << 108) * F::from_u128(1u128 << 108);
        let f_cm = f_c * F::from_u128(BUFMULT);
        let v = (f_c * F::from_u128(BUFMULT))
            + limbs[0].value * signs[0]
            + limbs[1].value * signs[1]
            + limbs[2].value * signs[2];
        let q = field_to_bn(&v).div(field_to_bn(&f_c));
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
                None,
            ],
            [
                Some(-f_c),
                Some(signs[0]),
                Some(signs[1]),
                Some(signs[2]),
                None,
                None,
                None,
                None,
                Some(f_cm),
            ],
            1, // check rcell range
        )?;
        Ok(())
    }

    /// constraints for (rhs * lhs) % modulus = result
    /// (x0,x1,x2) * (y0,y1,y2) = (q0,q1,q2) * (m0,m1,m2) + r0,r1,r2
    /// mod 2^{108}-1:
    ///    (x2+x1+x0)*(y0+y1+y2) = (q0+q1+q2)*(m0+m1+m2)+(r0+r1+r2)
    /// mod 2^{216}:
    ///    (x1*y0+x0*y1)*2^216+x0*y0 = (q0*m1+q1*m0)*2^{216}+q0*m0+r1+r0
    /// native:
    ///   x*y = q*m + r
    fn mod_mult(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Number<F>,
        rhs: &Number<F>,
        modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let bn_lhs = lhs.to_bn();
        let bn_rhs = rhs.to_bn();
        let bn_mult = bn_lhs.mul(bn_rhs);
        let bn_modulus = modulus.to_bn();
        let bn_quotient = bn_mult.clone().div(bn_modulus.clone()); //div_rem
        let bn_rem = bn_mult - (bn_quotient.clone() * bn_modulus.clone());
        let modulus = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&bn_modulus),
        )?;
        let rem = self.assign_number(region, range_check_chip, offset, Number::from_bn(&bn_rem))?;
        let quotient = self.assign_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&bn_quotient),
        )?;
        let mod_108m1_lhs = self.mod_power108m1_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_108m1_rhs =
            self.mod_power108m1_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let [r0, r1, r2, mod_108m1_rem] =
            self.mod_power108m1(region, range_check_chip, offset, &rem)?;
        self.mod_power108m1_zero(
            region,
            range_check_chip,
            offset,
            vec![
                mod_108m1_lhs.clone(),
                mod_108m1_rhs.clone(),
                mod_108m1_rem.clone(),
            ],
            vec![F::one(), -F::one(), -F::one()],
        )?;
        let mod_216_lhs = self.mod_power216_mul(region, range_check_chip, offset, lhs, rhs)?;
        let mod_216_rhs =
            self.mod_power216_mul(region, range_check_chip, offset, &quotient, &modulus)?;
        let mod_216_rem = self.mod_power216(region, range_check_chip, offset, &rem)?;

        self.mod_power216_zero(
            region,
            range_check_chip,
            offset,
            vec![mod_216_lhs, mod_216_rhs, mod_216_rem],
            vec![F::one(), -F::one(), -F::one()],
        )?;
        let mod_native = self.mod_native_mul(region, range_check_chip, offset, &rem, &lhs, &rhs)?;
        Ok(Number {
            limbs: [r0, r1, r2, mod_native],
        })
    }

    /// Selects result based on the condition exp_bit = '1' or '0' \
    ///
    /// # Arguments
    ///
    /// * `cond` - the exp_bit as a Limb in F, is only 0x1 or 0x0
    /// * `base` - the value of the base as a Number<F>
    /// * `one`  - the value of 1 as a Number<F>
    fn select(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        cond: &Limb<F>,
        base: &Number<F>,
        one: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        for i in 0..4 {
            let l = self.config.select(
                region,
                range_check_chip,
                offset,
                cond,
                &one.limbs[i],
                &base.limbs[i],
                0,
            )?;
            limbs.push(l);
        }
        Ok(Number {
            limbs: limbs.try_into().unwrap(),
        })
    }

    /// base^exp mod modulus
    pub fn mod_exp(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        base: &Number<F>,
        exp: &Number<F>,
        modulus: &Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut limbs = vec![];
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[2],
            &mut limbs,
            40,
        )?; //256 - 216 = 40
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[1],
            &mut limbs,
            108,
        )?;
        self.config.decompose_limb(
            region,
            range_check_chip,
            offset,
            &exp.limbs[0],
            &mut limbs,
            108,
        )?;
        let mut acc = self.assign_constant_number(
            region,
            range_check_chip,
            offset,
            Number::from_bn(&BigUint::from(1 as u128)),
        )?;
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
    use crate::circuits::range::{RangeCheckChip, RangeCheckConfig};
    use crate::circuits::CommonGateConfig;
    use crate::utils::Limb;
    use crate::value_for_assign;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr;
    use num_bigint::BigUint;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };

    use super::{ModExpChip, Number};

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>,
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig,
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
            HelperChip { config }
        }

        fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
            let limb = cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig { limb }
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
                    || value_for_assign!(n.limbs[i].value),
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
                ],
            };
            Ok(n)
        }
    }

    use num_bigint::RandomBits;
    use rand::{thread_rng, Rng};
    const LIMB_WIDTH: usize = 108;

    use std::ops::{Div, Mul};

    #[derive(Clone, Debug)]
    struct TestConfig {
        modexpconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    macro_rules! impl_modexp_test_circuit {
        ($circuit_name:ident, $test_fn_name:ident, $testvec:expr, $( $synth:tt )*) => {

            struct $circuit_name {
                op_a: BigUint,
                op_b: BigUint,
                op_c: BigUint,
                op_d: BigUint,
                bn_test_res: BigUint,
            }

            impl Circuit<Fr> for $circuit_name {
                type Config = TestConfig;
                type FloorPlanner = SimpleFloorPlanner;

                fn without_witnesses(&self) -> Self {
                    //Self::default()
                    unimplemented!();
                }

                fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
                    let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
                    Self::Config {
                        modexpconfig: ModExpChip::<Fr>::configure(meta, &rangecheckconfig),
                        helperconfig: HelperChip::configure(meta),
                        rangecheckconfig,
                    }
                }
                $( $synth )*
            }

            #[test]
            fn $test_fn_name() {
                fn run(test_circuit: $circuit_name) -> Result<(), CircuitError> {
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
                let testname = stringify!($test_fn_name);
                match testname {
                    "test_modpower108m1_circuit" => {
                        for testcase in $testvec {
                            let (op_a, _, _) = &testcase;
                            let (a_l2, a_l1, a_l0) = get_limbs_from_bn(&op_a);
                            let bn_l210sum = &a_l2 + &a_l1 + &a_l0;
                            let bn_test_res = bn_l210sum;
                            let op_b = BigUint::from(0u128);
                            let op_c = op_b.clone();
                            let op_d = op_b.clone();
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b,
                                op_c,
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    "test_modpower108m1mul_circuit" => {
                        for testcase in $testvec {
                            let (op_a, op_b, _) = &testcase;
                            let modulus = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
                            let bn_test_res = (op_a.clone() * op_b.clone()) % modulus;
                            let op_c = BigUint::from(0u128);
                            let op_d = op_c.clone();
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b: op_b.clone(),
                                op_c,
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    "test_modpower216mul_circuit" => {
                        for testcase in $testvec {
                            let (op_a, op_b, op_c) = &testcase;
                            let modulus = op_c.clone();
                            let bn_test_res = (op_a.clone() * op_b.clone()) % modulus;
                            let op_d = BigUint::from(0u128);
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b: op_b.clone(),
                                op_c: op_c.clone(),
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    "test_modpower108m1_vs_216_circuit" => {
                        for testcase in $testvec {
                            let (op_a, op_b, op_c) = &testcase;
                            let mult = op_a.clone().mul(op_b.clone());
                            let op_d = mult.clone().div(op_c.clone());   // quotient
                            let bn_test_res = mult - (op_d.clone() * op_c.clone());
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b: op_b.clone(),
                                op_c: op_c.clone(),
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    "test_mod_mult_circuit" => {
                        for testcase in $testvec {
                            let (op_a, op_b, op_c) = &testcase;
                            let lhs_testcase = op_a.clone();
                            let rhs_testcase = op_b.clone();
                            let modulus_testcase = op_c.clone();
                            let op_d = BigUint::from(0u128);
                            let bn_test_res =
                                (lhs_testcase.clone() * rhs_testcase.clone()) % modulus_testcase.clone();
                            println!(
                                "testcase: (0x{})*(0x{}) mod 0x{} = 0x{}",
                                lhs_testcase.clone().to_str_radix(16),
                                rhs_testcase.clone().to_str_radix(16),
                                modulus_testcase.clone().to_str_radix(16),
                                bn_test_res.to_str_radix(16)
                            );
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b: op_b.clone(),
                                op_c: op_c.clone(),
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    "test_modexp_circuit" => {
                        for testcase in $testvec {
                            let (op_a, op_b, op_c) = &testcase;
                            let base_testcase = op_a.clone();
                            let exp_testcase = op_b.clone();
                            let modulus_testcase = op_c.clone();
                            let bn_test_res = base_testcase
                                .clone()
                                .modpow(&exp_testcase, &modulus_testcase);
                            println!(
                                "testcase: (0x{})^(0x{}) mod 0x{} = 0x{}",
                                base_testcase.clone().to_str_radix(16),
                                exp_testcase.clone().to_str_radix(16),
                                modulus_testcase.clone().to_str_radix(16),
                                bn_test_res.to_str_radix(16)
                            );
                            let op_d = BigUint::from(0u128);
                            let test_circuit = $circuit_name {
                                op_a: op_a.clone(),
                                op_b: op_b.clone(),
                                op_c: op_c.clone(),
                                op_d,
                                bn_test_res
                            };
                            let output = run(test_circuit).expect(&format!("{} failed prover verify", testname));
                            println!("\n{} proof generation successful!\nresult: {:#?}", testname, output);
                        };
                    },
                    _ => {
                        println!("Unknown test...");
                    },
                }
            }
        };
    }

    // test circuits:
    impl_modexp_test_circuit!(
        TestModpower108m1Circuit,
        test_modpower108m1_circuit,
        testvectors_modpower108m1(),
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
                    let _ = &self.op_b;
                    let _ = &self.op_c;
                    let _ = &self.op_d;
                    let a = helperchip.assign_base(&mut region, &mut offset, &self.op_a)?;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let rem =
                        modexpchip.mod_power108m1(&mut region, &mut range_chip, &mut offset, &a)?;
                    println!("\nbn_res \t\t= 0x{}", &self.bn_test_res.to_str_radix(16));
                    println!("\nrem is (hex):");
                    for i in 0..4 {
                        println!("rem[{i}] \t\t= {:?}", &rem[i].value);
                    }
                    for i in 0..4 {
                        println!("result[{}] \t= {:?}", i, &result.limbs[i].value);
                        println!("resultcell[{}] \t= {:?}", i, &result.limbs[i].cell);
                        // region.constrain_equal(
                        //     rem.limbs[i].clone().cell.unwrap().cell(),
                        //     result.limbs[i].clone().cell.unwrap().cell()
                        // )?;
                    }
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    );

    impl_modexp_test_circuit!(
        TestModpower108m1mulCircuit,
        test_modpower108m1mul_circuit,
        testvectors_modpower108m1mul(),
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
                    let _ = &self.op_c;
                    let _ = &self.op_d;
                    let _result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let lhs = helperchip.assign_modulus(&mut region, &mut offset, &self.op_a)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.op_b)?;
                    let res = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    println!("\nbn_rem  \t= {:?}", &self.bn_test_res.to_str_radix(16));
                    println!("result is \t= {:?}", res.value);
                    Ok(res)
                },
            )?;
            Ok(())
        }
    );

    impl_modexp_test_circuit!(
        TestModPower216MulCircuit,
        test_modpower216mul_circuit,
        testvectors_modpower216mul(),
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
                    let _ = &self.op_c;
                    let _ = &self.op_d;
                    let _result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.op_a)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.op_b)?;
                    let res = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    println!("\nbn_rem \t= {}", &self.bn_test_res.to_str_radix(16));
                    println!("res \t= {:?}", res.value);
                    Ok(res)
                },
            )?;
            Ok(())
        }
    );

    impl_modexp_test_circuit!(
        Test108m1v216Circuit,
        test_modpower108m1_vs_216_circuit,
        testvectors_modp108m1vs216(),
        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
                || "test circuit 108m1 vs 216",
                |mut region| {
                    range_chip.initialize(&mut region)?;
                    let mut offset = 0;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.op_a)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.op_b)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.op_c)?;
                    let quo = helperchip.assign_base(&mut region, &mut offset, &self.op_d)?;
                    let rem =
                        helperchip.assign_base(&mut region, &mut offset, &self.bn_test_res)?;
                    let rl_mod_108m1 = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    let qm_mod_108m1 = modexpchip.mod_power108m1_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &quo,
                        &modulus,
                    )?;
                    let [_r0, _r1, _r2, rem_mod_108m1] = modexpchip.mod_power108m1(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &rem,
                    )?;
                    let lr_mod_216 = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                    )?;
                    let qm_mod_216 = modexpchip.mod_power216_mul(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &quo,
                        &modulus,
                    )?;
                    let rem_mod_216 =
                        modexpchip.mod_power216(&mut region, &mut range_chip, &mut offset, &rem)?;
                    println!(
                        "rl_mod_108m1  {:?} = {:?} lr_mod_216",
                        rl_mod_108m1.value, lr_mod_216.value
                    );
                    println!(
                        "qm_mod_108m1  {:?} = {:?} qm_mod_216",
                        qm_mod_108m1.value, qm_mod_216.value
                    );
                    println!(
                        "rem_mod_108m1 {:?} = {:?} mod_216_rem",
                        rem_mod_108m1.value, rem_mod_216.value
                    );
                    println!("");
                    region.constrain_equal(
                        rl_mod_108m1.clone().cell.unwrap().cell(),
                        lr_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    region.constrain_equal(
                        qm_mod_108m1.clone().cell.unwrap().cell(),
                        qm_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    region.constrain_equal(
                        rem_mod_108m1.clone().cell.unwrap().cell(),
                        rem_mod_216.clone().cell.unwrap().cell(),
                    )?;
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    );

    impl_modexp_test_circuit!(
        TestModMultCircuit,
        test_mod_mult_circuit,
        testvectors_modmult(),
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
                    let _ = &self.op_d;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.op_c)?;
                    let lhs = helperchip.assign_base(&mut region, &mut offset, &self.op_a)?;
                    let rhs = helperchip.assign_base(&mut region, &mut offset, &self.op_b)?;
                    let rem = modexpchip.mod_mult(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &lhs,
                        &rhs,
                        &modulus,
                    )?;
                    for i in 0..4 {
                        println!(
                            "rem is {:?}, result is {:?}",
                            &rem.limbs[i].value, &result.limbs[i].value
                        );
                        println!(
                            "remcell is {:?}, resultcell is {:?}",
                            &rem.limbs[i].cell, &result.limbs[i].cell
                        );
                        region.constrain_equal(
                            rem.limbs[i].clone().cell.unwrap().cell(),
                            result.limbs[i].clone().cell.unwrap().cell(),
                        )?;
                    }
                    Ok(rem)
                },
            )?;
            Ok(())
        }
    );

    impl_modexp_test_circuit!(
        TestModExpCircuit,
        test_modexp_circuit,
        testvectors_modexp(),
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
                    let _ = &self.op_d;
                    let base = helperchip.assign_base(&mut region, &mut offset, &self.op_a)?;
                    let exp = helperchip.assign_exp(&mut region, &mut offset, &self.op_b)?;
                    let modulus =
                        helperchip.assign_modulus(&mut region, &mut offset, &self.op_c)?;
                    let result =
                        helperchip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                    let rem = modexpchip.mod_exp(
                        &mut region,
                        &mut range_chip,
                        &mut offset,
                        &base,
                        &exp,
                        &modulus,
                    )?;
                    for i in 0..4 {
                        // println!("rem is {:?}, \t result is {:?}", &rem.limbs[i].value, &result.limbs[i].value);
                        // println!("remcell is \t{:?}", &rem.limbs[i].cell);
                        // println!("resultcell is \t {:?}", &result.limbs[i].cell);
                        region.constrain_equal(
                            rem.limbs[i].clone().cell.unwrap().cell(),
                            result.limbs[i].clone().cell.unwrap().cell(),
                        )?;
                    }
                    Ok(())
                },
            )?;
            Ok(())
        }
    );

    // test vectors:

    fn testvectors_modpower108m1() -> Vec<(BigUint, BigUint, BigUint)> {
        // Create an a set of test vectors varying in bit lengths.
        // Test will pass if:
        //  (1) result returned from circuit constrain_equal() to the
        //      assigned result from bn calculation.
        //  (2) prover.verify() for each run verifies without error.
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        let bit_len_a: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        for i in 0..8 {
            let (a, b, c) = (
                get_random_x_bit_bn(bit_len_a[i]),
                BigUint::from(0u128),
                BigUint::from(0u128),
            );
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    fn testvectors_modpower108m1mul() -> Vec<(BigUint, BigUint, BigUint)> {
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        let bit_len_a: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        let bit_len_b: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        for i in 0..8 {
            let (a, b, c) = (
                get_random_x_bit_bn(bit_len_a[i]),
                get_random_x_bit_bn(bit_len_b[i]),
                BigUint::from(0u128),
            );
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    fn testvectors_modpower216mul() -> Vec<(BigUint, BigUint, BigUint)> {
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        let bit_len_a: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        let bit_len_b: [usize; 8] = [
            0,
            1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + 108,
            LIMB_WIDTH + LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 108,
        ];
        let bit_len_c: [usize; 8] = [1, 2, 4, 8, 16, 32, 64, 100];
        for i in 0..8 {
            let (a, b, c) = (
                get_random_x_bit_bn(bit_len_a[i]),
                get_random_x_bit_bn(bit_len_b[i]),
                get_random_x_bit_bn(bit_len_c[i]),
            );
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    fn testvectors_modp108m1vs216() -> Vec<(BigUint, BigUint, BigUint)> {
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        // product of l and r cannot exceed LIMB_WIDTH bits or mod 108m1 != mod 216.
        // generate a random number up to L_BITLENGTH to use as the seed for the l bit length.
        // i.e., l (1-80-bits) * r (LIMB_WIDTH - (1-80-bits)) < (2^108)-1)
        const L_BITLENGTH: usize = 80;
        let mut rng = rand::thread_rng();
        let bit_len_c: [usize; 8] = [1, 2, 4, 8, 16, 32, 32, 32];
        for i in 0..8 {
            let (bn_a, bn_b) = get_random_product_not_exceed_n_bits(rng.gen_range(1..=L_BITLENGTH));
            let (a, b, c) = (bn_a, bn_b, get_random_x_bit_bn(bit_len_c[i]));
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    fn testvectors_modmult() -> Vec<(BigUint, BigUint, BigUint)> {
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        const NUM_TESTS: usize = 6;
        let bit_len_l: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH + 1,
        ];
        let bit_len_r: [usize; NUM_TESTS] = [
            1,
            4,
            8,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 36,
            LIMB_WIDTH + LIMB_WIDTH + 10, // + 12 will error
        ];
        let bit_len_m: [usize; NUM_TESTS] = [1, 4, 8, 12, 16, 20];
        for i in 0..NUM_TESTS {
            let (a, b, c) = (
                get_random_x_bit_bn(bit_len_l[i]),
                get_random_x_bit_bn(bit_len_r[i]),
                get_random_x_bit_bn(bit_len_m[i]),
            );
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    fn testvectors_modexp() -> Vec<(BigUint, BigUint, BigUint)> {
        let mut bn_test_vectors: Vec<(BigUint, BigUint, BigUint)> = Vec::with_capacity(8);
        const NUM_TESTS: usize = 5; // 100 finished in 573.17s
        let mut bit_len_b: [usize; NUM_TESTS] = [0; NUM_TESTS];
        let mut bit_len_m: [usize; NUM_TESTS] = [0; NUM_TESTS];
        let mut bit_len_e: [usize; NUM_TESTS] = [0; NUM_TESTS];
        let mut rng = rand::thread_rng();
        for i in 0..NUM_TESTS {
            bit_len_b[i] = rng.gen_range(1..16);
            bit_len_m[i] = rng.gen_range(1..16);
            bit_len_e[i] = rng.gen_range(1..(LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH - 90));
        }
        for i in 0..NUM_TESTS {
            let (a, b, c) = (
                get_random_x_bit_bn(bit_len_b[i]),
                get_random_x_bit_bn(bit_len_m[i]),
                get_random_x_bit_bn(bit_len_e[i]),
            );
            bn_test_vectors.push((a, b, c));
        }
        bn_test_vectors
    }

    // test helpers:
    use halo2_proofs::dev::VerifyFailure;
    use std::fmt;

    pub enum CircuitError {
        /// Thrown when `MockProver::run` fails to prove the circuit.
        ProverError(Error),
        /// Thrown when verification fails.
        VerifierError(Vec<VerifyFailure>),
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
            }
        }
    }

    /// # bn_limbs from BigUint
    /// Extracts BigUint to tuple of limbs \
    /// BigUint -> (l2,l1,l0)
    ///
    fn get_limbs_from_bn(bn: &BigUint) -> (BigUint, BigUint, BigUint) {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb1 = ((bn - limb0.clone()) / BigUint::from(1u128 << 108))
            .modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        let limb2 = (bn / BigUint::from(1u128 << 108)) / (BigUint::from(1u128 << 108));
        (limb2, limb1, limb0)
    }

    /// # random BigUint x-bits long
    /// returns a BigUint with bit length = bit_length
    fn get_random_x_bit_bn(bit_length: usize) -> BigUint {
        let mut rng = thread_rng();
        let mut b = BigUint::default();
        while b.bits() != bit_length as u64 {
            b = rng.sample(RandomBits::new(bit_length as u64));
        }
        b
    }

    /// # Returns two BigUint values whose product does not exceed LIMB_WIDTH bits.
    fn get_random_product_not_exceed_n_bits(n: usize) -> (BigUint, BigUint) {
        let vmax = BigUint::parse_bytes(b"fffffffffffffffffffffffffff", 16).unwrap();
        let b1 = get_random_x_bit_bn(n);
        let max_bits = LIMB_WIDTH - b1.bits() as usize;
        let mut b2 = vmax.clone();
        while (b2.clone() * b1.clone()) > vmax {
            b2 = get_random_x_bit_bn(max_bits);
        }
        (b1, b2)
    }
}
