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
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::circuit::layouter;
use halo2_proofs::plonk::*;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region},
    plonk::{
        ConstraintSystem, Error
    },
};
use std::marker::PhantomData;

pub struct BabyJubChip<F:FieldExt> {
    config: CommonGateConfig,
    _marker: PhantomData<F>
}



#[derive(Clone, Debug)]
pub struct Point<F: FieldExt> {
    x: Limb<F>,
    y: Limb<F>,
}

/*
impl<F: FieldExt> Point<F> {
}
*/

impl<F: FieldExt> Chip<F> for BabyJubChip<F> {
    type Config = CommonGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> BabyJubChip<F> {
    pub fn new(config: CommonGateConfig) -> Self {
        BabyJubChip {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>, range_check_config: &RangeCheckConfig) -> CommonGateConfig {
        CommonGateConfig::configure(cs, range_check_config)
    }

    pub fn add (
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Point<F>,
        rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        /* lambda = dx1x2y1y2
         * x3 = (x1y2 + y1x2)/(1 + lambda)
         * y3 = (y1y2 - x1x2)/(1 - lambda)
         */
        let x1x2 = lhs.x.value * rhs.x.value;
        let y1y2 = lhs.y.value * rhs.y.value;
        let lambda1 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(lhs.x.clone()),
                None,
                None,
                Some(rhs.x.clone()),
                Some(Limb::new(None, x1x2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0
        )?[4].clone();  // verify x1x2 is correct
        let lambda2 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(lhs.y.clone()),
                None,
                None,
                Some(rhs.y.clone()),
                Some(Limb::new(None, y1y2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0
        )?[4].clone();  // verify y1y2 is correct
        let lambda = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(lambda1),
                None,
                None,
                Some(lambda2),
                Some(Limb::new(None, y1y2 * x1x2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0
        )?[4].clone();  // lambda1*lambda2 = y1y2 * x1x2

        let x3_f = lhs.x.value * rhs.y.value + lhs.y.value * rhs.x.value;
        let x3s = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(lhs.x.clone()),
                Some(lhs.y.clone()),
                Some(rhs.x.clone()),
                Some(rhs.y.clone()),
                Some(Limb::new(None, x3_f)),
                None,
            ],
            [None, None, None, None, Some(F::one()), None, Some(F::one()), Some(F::one()), None],
            0
        )?[4].clone();   // gives limb of x3_f

        //x3 * (1+lambda) = x3s
        let x3_f = x3s.value * (F::one() + lambda.value).invert().unwrap();
        let x3 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, x3_f)),
                Some(x3s.clone()),
                None,
                Some(lambda.clone()),
                None,
                None,
            ],
            [Some(F::one()), Some(-F::one()), None, None, None, None, Some(F::one()), None, None],
            0
        )?[3].clone();  // this might give lambda



        let y3_f = lhs.y.value * rhs.y.value - lhs.x.value * rhs.x.value;
        let y3s = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(lhs.y.clone()),
                Some(lhs.x.clone()),
                Some(rhs.x.clone()),
                Some(rhs.y.clone()),
                Some(Limb::new(None, y3_f)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), Some(-F::one()), None],
            0
        )?[4].clone();

        //y3 * (1-lambda) = y3s
        let y3_f = y3s.value * (F::one() - lambda.value).invert().unwrap();
        let y3 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, y3_f)),
                Some(y3s.clone()),
                None,
                Some(lambda.clone()),
                None,
                None,
            ],
            [Some(F::one()), Some(-F::one()), None, None, None, None, Some(-F::one()), None, None],
            0
        )?[3].clone();
        Ok(Point {x: x3, y: y3})
    }

    pub fn mul_scalar(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        // parse the lhs to binary format
        // ret = O, additive identity on babyjub
        // for each bit {
        //     add(ret,ret)
        //     if bit == 1 {
        //         add(ret,P)
        //     }
        // }
        // Ok(ret)
        let mut scalar_bin: Vec<Limb<F>> = vec![];
        self.config.decompose_limb(region, range_check_chip, offset, lhs, &mut scalar_bin, 4)?;   
        // get the additive identity point
        let iden_ele = Point{x: Limb::new(None, F::zero()), y: Limb::new(None, F::one())};
        // constrain it by adding to itself must still be itself
        let iden_ele_plus_iden_ele = self.add(region, range_check_chip, offset, &mut iden_ele.clone(), &mut iden_ele.clone())?;   
        // I try to constrain that e +e = e so that it must be identity point
        // Im not sure if this is necessary
        let e_x = self.config.assign_line(region, range_check_chip, offset,
            [
                None,
                Some(iden_ele_plus_iden_ele.x.clone()),
                None,
                Some(iden_ele.x.clone()),
                None,
                None,
            ],
            [None, Some(F::one()), None, Some(-F::one()), None, None, None, None, None],
            0
        )?[3].clone();

        let e_y = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(iden_ele_plus_iden_ele.y.clone()),
                None,
                Some(iden_ele.y.clone()),
                None,
                None,
                None,
            ],
            [Some(F::one()), None, Some(-F::one()), None, None, None, None, None, None],
            0
        )?[2].clone();

        // start with additive identity
        let ret = Point { x: e_x.clone(), y: e_y.clone()};

        // loop through the decomposed limbs
        for limb in scalar_bin {    // each limb has val either one or zero
            // add to itself everytime
            let ret = self.add(region, range_check_chip, offset, &ret.clone(), &ret.clone())?;  
            // add the original point iff the limb val is 1
            let add_x = self.config.select(region, range_check_chip, offset, &limb, &rhs.clone().x, &e_x.clone())?;
            let add_y = self.config.select(region, range_check_chip, offset, &limb, &rhs.clone().y, &e_y.clone())?;
            // point to add will be the additive identity if current digit is 0, will be original point o.w
            let point_to_add = Point{x: add_x, y: add_y};
            let ret = self.add(region, range_check_chip, offset, &ret.clone(), &point_to_add)?;
        } 
        Ok(ret)

        

    }

}

#[cfg(test)]
mod tests {
    use poseidon_rs::Poseidon;
    use std::str::FromStr;
    pub type Pfr = poseidon_rs::Fr; // alias
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
            Advice, Instance, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        BabyJubChip,
        Point,
        Limb,
    };

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        ret_x: Column<Advice>,
        ret_y: Column<Advice>,
        p1_x: Column<Advice>,
        p1_y: Column<Advice>,
        p2_x: Column<Advice>,
        p2_y: Column<Advice>,
        known_x: Column<Advice>,
        known_y: Column<Advice>,
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

        fn configure(cs: &mut ConstraintSystem<Fr>,
            
        ) -> HelperChipConfig {
            let p1_x = cs.advice_column();
            let p1_y = cs.advice_column();
            let p2_x = cs.advice_column();
            let p2_y= cs.advice_column();
            let known_x = cs.advice_column();
            let known_y= cs.advice_column();
            let ret_x= cs.advice_column();
            let ret_y= cs.advice_column();

            cs.enable_equality(ret_x);
            cs.enable_equality(ret_y);
            cs.enable_equality(known_x);
            cs.enable_equality(known_y);
            HelperChipConfig {
                ret_x,
                ret_y,
                p1_x,
                p1_y,
                p2_x,
                p2_y,
                known_x,
                known_y,
            }
        }

        fn assign_p1(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            x_val: Fr,
            y_val: Fr,
        ) -> Result<Point<Fr>, Error> {
            let x = region.assign_advice(
                || "p1 x",
                self.config.p1_x,
                *offset, // rotation
                || value_for_assign!(x_val),
            )?;
            
            let y = region.assign_advice(
                || "p1 y",
                self.config.p1_y,
                *offset, 
                ||value_for_assign!(y_val),
            )?;

            Ok(Point {x: Limb::new(Some(x), x_val), y: Limb::new(Some(y), y_val)})
        }

        fn assign_p2(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            x_val: Fr,
            y_val: Fr,
        ) -> Result<Point<Fr>, Error> {
            let x = region.assign_advice(
                || "p2 x",
                self.config.p2_x,
                *offset, // rotation
                || value_for_assign!(x_val),
            )?;
            
            let y = region.assign_advice(
                || "p2 y",
                self.config.p2_y,
                *offset, 
                ||value_for_assign!(y_val),
            )?;

            Ok(Point {x: Limb::new(Some(x), x_val), y: Limb::new(Some(y), y_val)})
        }


        fn assign_addition_result(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            p: &Point<Fr>,
        ) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
            let x = region.assign_advice(
                || "ret_x",
                self.config.ret_x,
                *offset, // rotation
                || value_for_assign!(p.x.value),
            )?;
            
            let y = region.assign_advice(
                || "ret_y",
                self.config.ret_y,
                *offset, 
                ||value_for_assign!(p.y.value),
            )?;

            Ok((Limb::new(Some(x), p.x.value), Limb::new(Some(y), p.y.value)))
        }

        fn assign_known_val(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            x_val: Fr,
            y_val: Fr,
        ) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
            let x = region.assign_advice(
                || "p1 x",
                self.config.known_x,
                *offset, // rotation
                || value_for_assign!(x_val),
            )?;
            
            let y = region.assign_advice(
                || "p1 y",
                self.config.known_y,
                *offset, 
                ||value_for_assign!(y_val),
            )?;

            Ok((Limb::new(Some(x), x_val), Limb::new(Some(y), y_val)))
        }
        
        // we have two points in the circuit and we add them up and get the third point
        // which we assign to the advice column in the circuit
        // then we constrain that to be equal to a correct result 

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        p1_x: Fr,
        p1_y: Fr,
        p2_x: Fr,
        p2_y: Fr,
        known_x: Fr,
        known_y: Fr, 

    }
    
    #[derive(Clone, Debug)]
    struct TestConfig {
        babyjubconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>,
        ) -> Self::Config {
            let rangecheckconfig = RangeCheckChip::<Fr>::configure(meta);
            Self::Config {
                babyjubconfig: BabyJubChip::<Fr>::configure(meta, &rangecheckconfig),
                helperconfig: HelperChip::configure(meta),
                rangecheckconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let babyjubchip = BabyJubChip::<Fr>::new(config.clone().babyjubconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            let mut range_chip = RangeCheckChip::<Fr>::new(config.clone().rangecheckconfig);
            layouter.assign_region(
            || "test addition",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                // point 1
                let p1 = helperchip.assign_p1(&mut region, &mut offset, self.p1_x, self.p1_y)?;
                let p2 = helperchip.assign_p2(&mut region, &mut offset, self.p2_x, self.p2_y)?;
                let p3 = babyjubchip.add(&mut region, &mut range_chip, &mut offset, & p1, &p2)?;
                let (x,y) = helperchip.assign_addition_result(&mut region, &mut offset, & p3)?;
                let (fixed_x, fixed_y) = helperchip.assign_known_val(&mut region, &mut offset, self.known_x, self.known_y)?;
                region.constrain_equal(x.clone().cell.unwrap().cell(), fixed_x.clone().cell.unwrap().cell())?;
                region.constrain_equal(y.clone().cell.unwrap().cell(), fixed_y.clone().cell.unwrap().cell())?;
                Ok(())
            })
        }
    }

    #[test]
    fn test_circuit() {
        let p1_x =  Fr::from_raw(
            [0x0de0b6b3a7640000,
            0xc48b104f04900100,
            0x1a64e9041709a8b3,
            0x628a7dae9ba4b1e0]
        );
        let p1_y = Fr::from_raw(
            [0x0a8c6e8170c01000,
            0x5b0cde19e5f4f50a,
            0x0f1538c00a002500,
            0x5ba2c0db80bff0c0]
        ); 

        let p2_x =  Fr::from_raw(
            [0x5319749e6cfc025c,
            0x8899c43fa6e5589e,
            0x0b4fe466a0649411,
            0x2352c7aef937bddc]
        );
        let p2_y = Fr::from_raw(
            [0x2b548aeec5285dd7,
            0x68de7ca7bb0c30ab,
            0x4f2aee6a9f2a9575,
            0x1889e3c23b9a1f2f]
        );


        let known_x =  Fr::from_raw(
            [0x6e27e1a95a909dcc,
            0x0c30904d23abaa40,
            0x235cc4e377f91c5f,
            0x13edc339108d63b1]
        );
        let known_y = Fr::from_raw(
            [0xb2fe7e032775d019,
            0x07f1c9ae4d655f5b,
            0xf9d66a74be03f788,
            0x6d81e00a734c3bb1]
        );

        let test_circuit = TestCircuit {
            p1_x,
            p1_y,
            p2_x,
            p2_y,
            known_x, 
            known_y} ;
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}