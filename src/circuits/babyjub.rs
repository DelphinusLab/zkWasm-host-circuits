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

    // pub fn add_org (
    //     &self,
    //     region: &mut Region<F>,
    //     range_check_chip: &mut RangeCheckChip<F>,
    //     offset: &mut usize,
    //     lhs: &Point<F>,
    //     rhs: &Point<F>,
    // ) -> Result<Point<F>, Error> {
    //     /* lambda = dx1x2y1y2
    //      * x3 = (x1y2 + y1x2)/(1 + lambda)
    //      * y3 = (y1y2 - x1x2)/(1 - lambda)
    //      */
    //     // constants
    //     let a = F::from(168700);
    //     let d = F::from(168696);
    //     let x1x2 = lhs.x.value * rhs.x.value;
    //     let y1y2 = lhs.y.value * rhs.y.value;
    //     let lambda1 = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(lhs.x.clone()),
    //             None,
    //             None,
    //             Some(rhs.x.clone()),
    //             Some(Limb::new(None, x1x2)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
    //         0
    //     )?[4].clone();  // verify x1x2 is correct
    //     let lambda2 = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(lhs.y.clone()),
    //             None,
    //             None,
    //             Some(rhs.y.clone()),
    //             Some(Limb::new(None, y1y2)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
    //         0
    //     )?[4].clone();  // verify y1y2 is correct
    //     let lambda = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(lambda1),
    //             None,
    //             None,
    //             Some(lambda2),
    //             Some(Limb::new(None, y1y2 * x1x2)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
    //         0
    //     )?[4].clone();  // lambda1*lambda2 = y1y2 * x1x2
    //     let x3_f = lhs.x.value * rhs.y.value + lhs.y.value * rhs.x.value;
    //     let x3s = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(lhs.x.clone()),
    //             Some(lhs.y.clone()),
    //             Some(rhs.x.clone()),
    //             Some(rhs.y.clone()),
    //             Some(Limb::new(None, x3_f)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(F::one()), None, Some(F::one()), Some(F::one()), None],
    //         0
    //     )?[4].clone();   // gives limb of x3_f, which is x1y2 + x2y1
    //     // x3 * (1+d*lambda) = x3s
    //     // need to mul by d here, which is 168696
    //     let x3_f = x3s.value * (F::one() + d*lambda.value).invert().unwrap();
    //     let x3 = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(Limb::new(None, x3_f)),
    //             Some(x3s.clone()),
    //             None,
    //             Some(lambda.clone()),
    //             None,
    //             None,
    //         ],
    //         [Some(F::one()), Some(-F::one()), None, None, None, None, Some(F::one()), None, None],
    //         0
    //     )?[3].clone();  
    //     // neee to be lhs.y.value * rhs.y.value - a*lhs.x.value * rhs.x.value
    //     // a = 168700
    //     let y3_f = lhs.y.value * rhs.y.value - a * lhs.x.value * rhs.x.value;
    //     let y3s = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(lhs.y.clone()),
    //             Some(lhs.x.clone()),
    //             Some(rhs.x.clone()),
    //             Some(rhs.y.clone()),
    //             Some(Limb::new(None, y3_f)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::one()), Some(-F::one()), None],
    //         0
    //     )?[4].clone(); // gives y1y2 - ax1x2
    //     // y3 * (1-d* lambda) = y3s
    //     // missing d here
    //     let y3_f = y3s.value * (F::one() - d * lambda.value).invert().unwrap();
    //     let y3 = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(Limb::new(None, y3_f)),
    //             Some(y3s.clone()),
    //             None,
    //             Some(lambda.clone()),
    //             None,
    //             None,
    //         ],
    //         [Some(F::one()), Some(-F::one()), None, None, None, None, Some(-F::one()), None, None],
    //         0
    //     )?[3].clone();
    //     Ok(Point {x: x3, y: y3})
    // }

    // pub fn point_double(
    //     &self,
    //     region: &mut Region<F>,
    //     range_check_chip: &mut RangeCheckChip<F>,
    //     offset: &mut usize,
    //     point: &Point<F>,
    // ) -> Result<Point<F>, Error> {
    //     // constants
    //     let a = F::from(168700);
    //     let d = F::from(168696);

    //     let lambda1_t = F::from(3) * point.clone().x.value * point.clone().x.value + a;
    //     let lambda1 = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(Limb::new(None, point.x.clone().value)),
    //             None,
    //             None,
    //             Some(Limb::new(None, point.x.clone().value)),
    //             Some(Limb::new(None, lambda1_t)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::from(3)), None, Some(a)],
    //         0,
    //     )?[2].clone();
    //     let lambda2_t = (F::from(2) * point.clone().y.value).invert().unwrap();
    //     let lambda = self.config.assign_line(region, range_check_chip, offset,
    //         [
    //             Some(Limb::new(None, lambda2_t)),
    //             None,
    //             None,
    //             Some(lambda1),
    //             Some(Limb::new(None, lambda1_t)),
    //             None,
    //         ],
    //         [None, None, None, None, Some(-F::one()), None, Some(F::from(3)), None, None],
    //         0,
    //     )?[2].clone();
    // }

    pub fn mul_scalar(
        &self,
        region: &mut Region<F>,
        range_check_chip: &mut RangeCheckChip<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        let mut scalar_bin: Vec<Limb<F>> = vec![];
        self.config.decompose_limb(region, range_check_chip, offset, lhs, &mut scalar_bin, 4)?;   

        // get the additive identity point
        let iden_ele = Point{x: Limb::new(None, F::zero()), y: Limb::new(None, F::one())};

        let mut ret = iden_ele.clone();
        let mut temp = rhs.clone();
        // loop through the decomposed limbs
        for limb in scalar_bin.iter().rev() {    // each limb has val either one or zero
            // add the temp point iff the limb val is 1
            let add_x = self.config.select(region, range_check_chip, offset, &limb, &Limb::new(None, iden_ele.clone().x.value),&Limb::new(None, temp.clone().x.value),  0)?;
            // println!("{:?}", add_x);
            let add_y = self.config.select(region, range_check_chip, offset, &limb, &Limb::new(None, iden_ele.clone().y.value),&Limb::new(None, temp.clone().y.value),  0)?;
            // println!("{:?}", add_y);
            let point_to_add = Point{x: add_x, y: add_y}; // this would be identity element if the cond is not satisfied
            ret = self.add(region, range_check_chip, offset, &ret.clone(), &point_to_add.clone())?;  
            temp = self.add(region, range_check_chip, offset, &temp.clone(), &temp.clone())?;
        } 
        Ok(ret)

        

    }

    // stupid ver
    // pub fn mul_scalar(
    //     &self,
    //     region: &mut Region<F>,
    //     range_check_chip: &mut RangeCheckChip<F>,
    //     offset: &mut usize,
    //     lhs: &Limb<F>,
    //     rhs: &Point<F>,
    // ) -> Result<Point<F>, Error> {
    //     let mut ret = rhs.clone();
    //     ret = self.add(region, range_check_chip, offset, &ret.clone(), &ret.clone())?;
    //     Ok(ret)
    // }

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
        // constants
        let a = F::from(168700);
        let d = F::from(168696);

        // constraint lambda
        let x1x2 = lhs.x.value * rhs.x.value;
        
        let y1y2 = lhs.y.value * rhs.y.value;
        let lambda1 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, lhs.x.clone().value)),
                None,
                None,
                Some(Limb::new(None, rhs.x.clone().value)),
                Some(Limb::new(None, x1x2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0,
        )?[2].clone();  // verify x1x2 is correct

        let lambda2 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, lhs.y.clone().value)),
                None,
                None,
                Some(Limb::new(None, rhs.y.clone().value)),
                Some(Limb::new(None, y1y2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), None, None],
            0
        )?[2].clone();  // verify y1y2 is correct
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
        )?[2].clone();  // lambda1*lambda2 = y1y2 * x1x2

        let x3_f = lhs.x.value * rhs.y.value + lhs.y.value * rhs.x.value;
        let x3s = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, lhs.x.clone().value)),
                Some(Limb::new(None, lhs.y.clone().value)),
                Some(Limb::new(None, rhs.x.clone().value)),
                Some(Limb::new(None, rhs.y.clone().value)),
                Some(Limb::new(None, x3_f)),
                None,
            ],
            [None, None, None, None, Some(F::one()), None, Some(-F::one()), Some(-F::one()), None],
            0
        )?[4].clone();   // gives x1y2 + x2y1
        let x3_f = (F::one() + d*lambda.value).invert().unwrap();   // other part of x3
        // constrain x3 to be the product of the two
        let x3_t = x3s.value * x3_f;
        let x3 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, x3_f)),
                Some(Limb::new(None, x3_t)),
                None,
                Some(x3s.clone()),
                None,
                None,
            ],
            [None, Some(-F::one()), None, None, None, None, Some(F::one()), None, None],
            0
        )?[1].clone();  

        let y3_f = lhs.y.value * rhs.y.value - a * lhs.x.value * rhs.x.value;
        let y3s = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(Limb::new(None, lhs.y.clone().value)),
                Some(Limb::new(None, lhs.x.clone().value)),
                Some(Limb::new(None, rhs.x.clone().value)),
                Some(Limb::new(None, rhs.y.clone().value)),
                Some(Limb::new(None, y3_f)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), Some(-a), None],
            0
        )?[4].clone(); // gives y1y2 - ax1x2
        let y3_2 = (F::one() - d*lambda.value).invert().unwrap();
        // let y3_f = self.config.assign_line(region, range_check_chip, offset,
        //     [
        //         Some(Limb::new(None, d)),
        //         Some(Limb::new(None, y3_2)),
        //         None,
        //         Some(lambda.clone()),
        //         None,
        //         None,
        //     ],
        //     [None, Some(-F::one()), None, None, None, None, Some(-F::one()), None, Some(F::one())],
        //     0
        // )?[1].clone();
        let y3_t = y3s.value * y3_2;
        // constrain it
        let y3 = self.config.assign_line(region, range_check_chip, offset,
            [
                Some(y3s.clone()),
                Some(Limb::new(None, y3_t)),
                None,
                Some(Limb::new(None, y3_2)),
                None,
                None,
            ],
            [None, Some(F::one()), None, None, None, None, Some(-F::one()), None, None],
            0
        )?[1].clone();



        Ok(Point {x: x3, y: y3})
    }
    

}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
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
    struct AddTestCircuit {
        p1_x: Fr,
        p1_y: Fr,
        p2_x: Fr,
        p2_y: Fr,
        known_x: Fr,
        known_y: Fr, 

    }
    
    #[derive(Clone, Debug)]
    struct AddTestConfig {
        babyjubconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    impl Circuit<Fr> for AddTestCircuit {
        type Config = AddTestConfig;
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
            // addition test
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
                // println!("{:?} \n", p1);
                // println!("{:?} \n", p2);
                let (fixed_x, fixed_y) = helperchip.assign_known_val(&mut region, &mut offset, self.known_x, self.known_y)?;
                region.constrain_equal(x.clone().cell.unwrap().cell(), fixed_x.clone().cell.unwrap().cell())?;
                region.constrain_equal(y.clone().cell.unwrap().cell(), fixed_y.clone().cell.unwrap().cell())?;
                Ok(())
            })
        }
    }

    #[derive(Clone, Debug, Default)]
    struct MulTestCircuit {
        p1_x: Fr,
        p1_y: Fr,
        mul_result_x: Fr,
        mul_result_y: Fr, 

    }
    
    #[derive(Clone, Debug)]
    struct MulTestConfig {
        babyjubconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
        rangecheckconfig: RangeCheckConfig,
    }

    impl Circuit<Fr> for MulTestCircuit {
        type Config = MulTestConfig;
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
            // addition test
            layouter.assign_region(
            || "test addition",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                // point 1
                let p1 = helperchip.assign_p1(&mut region, &mut offset, self.p1_x, self.p1_y)?;
                let p3 = babyjubchip.mul_scalar(&mut region, &mut range_chip, &mut offset, & Limb::new(None, Fr::from(2)), &p1)?;
                let (x,y) = helperchip.assign_addition_result(&mut region, &mut offset, & p3)?;
                // println!("{:?} \n", p1);
                // println!("{:?} \n", p2);
                let (fixed_x, fixed_y) = helperchip.assign_known_val(&mut region, &mut offset, self.mul_result_x, self.mul_result_y)?;
                region.constrain_equal(x.clone().cell.unwrap().cell(), fixed_x.clone().cell.unwrap().cell())?;
                region.constrain_equal(y.clone().cell.unwrap().cell(), fixed_y.clone().cell.unwrap().cell())?;
                Ok(())
            })
        }
    }

    #[derive(Clone, Debug, Default)]
    struct MulTestCircuit_2 {
        p1_x: Fr,
        p1_y: Fr,
        mul_result_x_2: Fr,
        mul_result_y_2: Fr, 

    }

    impl Circuit<Fr> for MulTestCircuit_2 {
        type Config = MulTestConfig;
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
            // addition test
            layouter.assign_region(
            || "test addition",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                // point 1
                let p1 = helperchip.assign_p1(&mut region, &mut offset, self.p1_x, self.p1_y)?;
                let p3 = babyjubchip.mul_scalar(&mut region, &mut range_chip, &mut offset, & Limb::new(None, Fr::from(5)), &p1)?;
                let (x,y) = helperchip.assign_addition_result(&mut region, &mut offset, & p3)?;
                // println!("{:?} \n", p1);
                // println!("{:?} \n", p2);
                let (fixed_x, fixed_y) = helperchip.assign_known_val(&mut region, &mut offset, self.mul_result_x_2, self.mul_result_y_2)?;
                region.constrain_equal(x.clone().cell.unwrap().cell(), fixed_x.clone().cell.unwrap().cell())?;
                region.constrain_equal(y.clone().cell.unwrap().cell(), fixed_y.clone().cell.unwrap().cell())?;
                Ok(())
            })
        }
    }

    #[test]
    fn test_circuit_add() {
        let p1_x =  Fr::from_raw(
            [0x6adb52fc9ee7a82c,
            0x9de555e0ba6a693c,
            0x9bc0d49fa725bddf,
            0x274dbce8d1517996]
        );
        let p1_y = Fr::from_raw(
            [0x4595febfd51eb853,
            0xb2e78246231640b5,
            0xe2eae9a542bd99f6,
            0x5ce98c61b05f47f,]
        ); 

        let p2_x =  Fr::from_raw(
            [0x79f2349047d5c157,
            0xc88fee14d607cbe7,
            0x6e35bc47bd9afe6c,
            0x2491aba8d3a191a7]
        );
        let p2_y = Fr::from_raw(
            [0x348dd8f7f99152d7,
            0xf9a9d4ed0cb0c1d1,
            0x18dbddfd24c35583,
            0x2e07297f8d3c3d78]
        );


        let known_x =  Fr::from_raw(
            [0x9067a2afaebaf361,
            0x72dded51978190e1,
            0xb3b811eaacd0ec7c,
            0x11805510440a3488]
        );
        let known_y = Fr::from_raw(
            [0xa100dd448e072c13,
            0xa89a9027777af9f,
            0xf9ff77744a39298a,
            0x1f07aa1b3c598e2f]
        );

        let test_circuit = AddTestCircuit {
            p1_x,
            p1_y,
            p2_x,
            p2_y,
            known_x, 
            known_y} ;
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

    }

    #[test]
    fn test_mul_2() {
        // point doubling
        let p1_x =  Fr::from_raw(
            [0x6adb52fc9ee7a82c,
            0x9de555e0ba6a693c,
            0x9bc0d49fa725bddf,
            0x274dbce8d1517996]
        );
        let p1_y = Fr::from_raw(
            [0x4595febfd51eb853,
            0xb2e78246231640b5,
            0xe2eae9a542bd99f6,
            0x5ce98c61b05f47f,]
        ); 

        let mul_result_x = Fr::from_raw(
            [0x5b3b889296901ab5,
            0xd661502728609ff9,
            0x47dd9e705eb5a3e8,
            0xf3c160e26fc96c3]
        );

        let mul_result_y = Fr::from_raw(
            [0x4f79dfed17eb14e1,
            0xe315c5cafe683a06,
            0x5585107619130e62,
            0x9979273078b5c73]
        );

        let test_circuit = MulTestCircuit {
            p1_x,
            p1_y,
            mul_result_x, 
            mul_result_y} ;

        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_mul_5(){
        let p1_x =  Fr::from_raw(
            [0x6adb52fc9ee7a82c,
            0x9de555e0ba6a693c,
            0x9bc0d49fa725bddf,
            0x274dbce8d1517996]
        );
        let p1_y = Fr::from_raw(
            [0x4595febfd51eb853,
            0xb2e78246231640b5,
            0xe2eae9a542bd99f6,
            0x5ce98c61b05f47f,]
        ); 

        let mul_result_x_2 = Fr::from_raw(
            [0x4448504e4f0a8ea8, 
            0xefd17858bd207580, 
            0x28d83f8c4a0a3dda, 
            0x2723a3dcd9609835]
        );

        let mul_result_y_2 = Fr::from_raw(
            [0x1afe6d363cc2d5c2,
            0xf8d412e85a02b902,
            0x772501db135cf420,
            0x0cb91505b04fa754]
        );

        let test_circuit = MulTestCircuit_2 {
            p1_x,
            p1_y,
            mul_result_x_2, 
            mul_result_y_2} ;

        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

}