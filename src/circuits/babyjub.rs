use crate::circuits::{
    CommonGateConfig,
    Limb,
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Chip, Region},
    plonk::{
        ConstraintSystem, Error
    },
};
use std::marker::PhantomData;

pub struct AltJubChip<F:FieldExt> {
    pub config: CommonGateConfig,
    state: JubState<F>,
    _marker: PhantomData<F>
}



#[derive(Clone, Debug)]
pub struct Point<F: FieldExt> {
    pub x: Limb<F>,
    pub y: Limb<F>,
}

pub struct JubState<F: FieldExt> {
    acc: Point<F>,
    default: Point<F>,
}

impl<F: FieldExt> Chip<F> for AltJubChip<F> {
    type Config = CommonGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> JubState<F> {
    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero = config.assign_constant(region, &mut (), offset, &F::zero())?;
        let one = config.assign_constant(region, &mut (), offset, &F::one())?;
        self.acc = Point {
            x: zero.clone(),
            y: one.clone(),
        };
        self.default = Point {
            x: zero,
            y: one,
        };
        Ok(())
    }
}

impl<F: FieldExt> AltJubChip<F> {
    pub fn new(config: CommonGateConfig) -> Self {
        let state = JubState {
            acc: Point {
                x: Limb::new(None, F::zero()),
                y: Limb::new(None, F::one()),
            },
            default: Point {
                x: Limb::new(None, F::zero()),
                y: Limb::new(None, F::one()),
            },
        };
        AltJubChip {
            config,
            state,
            _marker: PhantomData,
        }
    }

    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.state.initialize(config, region, offset)

    }

    pub fn assign_incremental_msm(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        point: &Point<F>,
        scalar: &Limb<F>,
        reset: &Limb<F>,
        result: &Point<F>,
    ) -> Result<(), Error> {
        self.state.acc.x = self.config.select(
            region,
            &mut (),
            offset,
            &reset,
            &self.state.acc.x,
            &self.state.default.x,
            0
        )?;

        self.state.acc.y = self.config.select(
            region,
            &mut (),
            offset,
            &reset,
            &self.state.acc.y,
            &self.state.default.y,
            0
        )?;

        let operand = self.mul_scalar(
            region,
            offset,
            scalar,
            point,
        )?;

        let acc = self.add(
            region,
            offset,
            &self.state.acc,
            &operand
        )?;

        self.state.acc = acc;
        region.constrain_equal(
            result.x.cell.as_ref().unwrap().cell(),
            self.state.acc.x.cell.as_ref().unwrap().cell()
        )?;

        region.constrain_equal(
            result.y.cell.as_ref().unwrap().cell(),
            self.state.acc.y.cell.as_ref().unwrap().cell()
        )?;
        Ok(())
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> CommonGateConfig {
        CommonGateConfig::configure(cs, &())
    }

    pub fn add (
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Point<F>,
        rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        /* lambda = dx1x2y1y2
         * x3 = (x1y2 + y1x2)/(1 + lambda)
         * y3 = (y1y2 - ax1x2)/(1 - lambda)
         */
        // constants
        let a = F::from_str_vartime("21888242871839275222246405745257275088548364400416034343698204186575808495616").unwrap();
        let d = F::from_str_vartime("12181644023421730124874158521699555681764249180949974110617291017600649128846").unwrap();

        // constraint lambda
        let x1x2 = lhs.x.value * rhs.x.value;

        let y1y2 = lhs.y.value * rhs.y.value;
        let lambda1 = self.config.assign_line(region, &mut (), offset,
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
        )?[2].clone();  // verify x1x2 is correct

        let lambda2 = self.config.assign_line(region, &mut (), offset,
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
        )?[2].clone();  // verify y1y2 is correct
        let d_lambda = self.config.assign_line(region, &mut (), offset,
            [
                Some(lambda1),
                None,
                None,
                Some(lambda2),
                Some(Limb::new(None, d*y1y2 * x1x2)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(d), None, None],
            0
        )?[2].clone();  // lambda1*lambda2 = y1y2 * x1x2

        let x3_f = lhs.x.value * rhs.y.value + lhs.y.value * rhs.x.value;
        let x3_f_cell = self.config.assign_line(region, &mut (), offset,
            [
                Some(lhs.x.clone()),
                Some(lhs.y.clone()),
                Some(rhs.x.clone()),
                Some(rhs.y.clone()),
                Some(Limb::new(None, x3_f)),
                None,
            ],
            [None, None, None, None, Some(F::one()), None, Some(-F::one()), Some(-F::one()), None],
            0
        )?[4].clone();   // gives x1y2 + x2y1


        //1+d*lambda
        let x_d_lambda = F::one() + d_lambda.value;
        let x_d_lambda_cell = self.config.assign_line(region, &mut (), offset,
            [
                 Some(Limb::new(None, x_d_lambda)),
                 Some(d_lambda.clone()),
                 None,
                 None,
                 None,
                 None,
            ],
            [Some(-F::one()), Some(F::one()), None, None, None, None, None, None, Some(F::one())],
            0
        )?[0].clone();

        let x_d_lambda_inv = (F::one() + d_lambda.value).invert().unwrap();
        let x_d_lambda_inv_cell = self.config.assign_line(region, &mut (), offset,
            [
                 Some(Limb::new(None, x_d_lambda_inv)),
                 None,
                 None,
                 Some(x_d_lambda_cell),
                 None,
                 None,
            ],
            [None, None, None, None, None, None, Some(-F::one()), None, Some(F::one())],
            0
        )?[0].clone();

        //x3 * (1+d*lambda) = x3f
        // constrain x3 to be the product of the two
        let x3_t = x_d_lambda_inv_cell.value * x3_f;
        let x3 = self.config.assign_line(region, &mut (), offset,
            [
                 Some(x3_f_cell),
                 Some(Limb::new(None, x3_t)),
                 None,
                 Some(x_d_lambda_inv_cell),
                 None,
                 None,
            ],
            [None, Some(-F::one()), None, None, None, None, Some(F::one()), None, None],
            0
        )?[1].clone();

        // gives y1y2 - ax1x2
        let y3_f = lhs.y.value * rhs.y.value - a * lhs.x.value * rhs.x.value;
        let y3_f_cell = self.config.assign_line(region, &mut (), offset,
            [
                Some(lhs.y.clone()),
                Some(lhs.x.clone()),
                Some(rhs.x.clone()),
                Some(rhs.y.clone()),
                Some(Limb::new(None, y3_f)),
                None,
            ],
            [None, None, None, None, Some(-F::one()), None, Some(F::one()), Some(-a), None],
            0
        )?[4].clone();

        //1-d*lambda
        let y_d_lambda = F::one() - d_lambda.value;
        let y_d_lambda_cell = self.config.assign_line(region, &mut (), offset,
            [
                  Some(Limb::new(None, y_d_lambda)),
                  Some(d_lambda.clone()),
                  None,
                  None,
                  None,
                  None,
            ],
            [Some(-F::one()), Some(-F::one()), None, None, None, None, None, None, Some(F::one())],
            0
        )?[0].clone();

        let y_d_lambda_inv = y_d_lambda.invert().unwrap();
        let y_d_lambda_inv_cell = self.config.assign_line(region, &mut (), offset,
            [
                  Some(Limb::new(None, y_d_lambda_inv)),
                  None,
                  None,
                  Some(y_d_lambda_cell),
                  None,
                  None,
            ],
            [None, None, None, None, None, None, Some(-F::one()), None, Some(F::one())],
            0
        )?[0].clone();


        //y3 * (1-d*lambda) = y3f
        let y3_t = y_d_lambda_inv_cell.value * y3_f;
        // constrain it
        let y3 = self.config.assign_line(region, &mut (), offset,
            [
                Some(y3_f_cell),
                Some(Limb::new(None, y3_t)),
                None,
                Some(y_d_lambda_inv_cell),
                None,
                None,
            ],
            [None, Some(F::one()), None, None, None, None, Some(-F::one()), None, None],
            0
        )?[1].clone();

        Ok(Point {x: x3, y: y3})
    }


    pub fn mul_scalar(
        &self,
        region: &mut Region<F>,
        offset: &mut usize,
        lhs: &Limb<F>,
        rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        let mut scalar_bin: Vec<Limb<F>> = vec![];
        self.config.decompose_limb(region, &mut (), offset, lhs, &mut scalar_bin, 256)?;

        // get the additive identity point
        let iden_ele = Point{x: Limb::new(None, F::zero()), y: Limb::new(None, F::one())};

        let mut ret = iden_ele.clone();
        let mut temp = rhs.clone();
        // loop through the decomposed limbs
        for limb in scalar_bin.iter().rev() {    // each limb has val either one or zero
            // add the temp point iff the limb val is 1
            let add_x = self.config.select(region, &mut (), offset, &limb, &Limb::new(None, iden_ele.clone().x.value),&Limb::new(None, temp.clone().x.value),  0)?;
            let add_y = self.config.select(region, &mut (), offset, &limb, &Limb::new(None, iden_ele.clone().y.value),&Limb::new(None, temp.clone().y.value),  0)?;
            let point_to_add = Point{x: add_x, y: add_y}; // this would be identity element if the cond is not satisfied
            ret = self.add(region, offset, &ret.clone(), &point_to_add.clone())?;
            temp = self.add(region,  offset, &temp.clone(), &temp.clone())?;
        }
        Ok(ret)
    }


}

#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;

    use crate::value_for_assign;
    use crate::circuits::CommonGateConfig;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        AltJubChip,
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

            cs.enable_equality(p1_x);
            cs.enable_equality(p1_y);
            cs.enable_equality(p2_x);
            cs.enable_equality(p2_y);

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
        altjubconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for AddTestCircuit {
        type Config = AddTestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>,
        ) -> Self::Config {
            Self::Config {
                altjubconfig: AltJubChip::<Fr>::configure(meta),
                helperconfig: HelperChip::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let altjubchip = AltJubChip::<Fr>::new(config.clone().altjubconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            // addition test
            layouter.assign_region(
            || "test addition",
            |mut region| {
                let mut offset = 0;
                // point 1
                let p1 = helperchip.assign_p1(&mut region, &mut offset, self.p1_x, self.p1_y)?;
                let p2 = helperchip.assign_p2(&mut region, &mut offset, self.p2_x, self.p2_y)?;
                let p3 = altjubchip.add(&mut region,  &mut offset, & p1, &p2)?;
                let (x,y) = helperchip.assign_addition_result(&mut region, &mut offset, & p3)?;
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
        scalar: Fr,

    }

    #[derive(Clone, Debug)]
    struct MulTestConfig {
        altjubconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for MulTestCircuit {
        type Config = MulTestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>,
        ) -> Self::Config {
            Self::Config {
                altjubconfig: AltJubChip::<Fr>::configure(meta),
                helperconfig: HelperChip::configure(meta),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let altjubchip = AltJubChip::<Fr>::new(config.clone().altjubconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            // addition test
            layouter.assign_region(
            || "test addition",
            |mut region| {
                let mut offset = 0;
                // point 1
                let p1 = helperchip.assign_p1(&mut region, &mut offset, self.p1_x, self.p1_y)?;
                let p3 = altjubchip.mul_scalar(&mut region,  &mut offset, & Limb::new(None, self.scalar.clone()), &p1)?;
                let (x,y) = helperchip.assign_addition_result(&mut region, &mut offset, & p3)?;
                let (fixed_x, fixed_y) = helperchip.assign_known_val(&mut region, &mut offset, self.mul_result_x, self.mul_result_y)?;
                region.constrain_equal(x.clone().cell.unwrap().cell(), fixed_x.clone().cell.unwrap().cell())?;
                region.constrain_equal(y.clone().cell.unwrap().cell(), fixed_y.clone().cell.unwrap().cell())?;
                Ok(())
            })
        }
    }


    use ff::PrimeField;
    #[test]
    fn test_circuit_add() {
        let p1_x = Fr::from_str_vartime("898028665198864058503333284914344364614816950090712808757628136883156793612").unwrap();
        let p1_y = Fr::from_str_vartime("6951008159789259462992382539818770993282026734853958799488384266457965763612").unwrap();
        let p2_x = Fr::from_str_vartime("21237458262955047976410108958495203094252581401952870797780751629344472264183").unwrap();
        let p2_y = Fr::from_str_vartime("2544379904535866821506503524998632645451772693132171985463128613946158519479").unwrap();
        let known_x = Fr::from_str_vartime("16578885538864834913634152914207572829284688953553409301338692898630452314902").unwrap();
        let known_y = Fr::from_str_vartime("4039721622823844597861764938277547409353264496911078152703637653498156063315").unwrap();
        let test_circuit = AddTestCircuit {
            p1_x,
            p1_y,
            p2_x,
            p2_y,
            known_x,
            known_y
        };
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));


    }

    #[test]
    fn test_circuit_mul() {
        let p1_x = Fr::from_str_vartime("21237458262955047976410108958495203094252581401952870797780751629344472264183").unwrap();
        let p1_y = Fr::from_str_vartime("2544379904535866821506503524998632645451772693132171985463128613946158519479").unwrap();
        let mul_result_x = Fr::from_str_vartime("19669747898413870458863629521161089277913689400039595142733762095585723002084").unwrap();
        let mul_result_y = Fr::from_str_vartime("9877930256250505639648328887241932676754586687658209502285904431386979993214").unwrap();


        // point doubling
        let scalar = Fr::from(32195221423877958);
        let test_circuit_2 = MulTestCircuit {
            p1_x,
            p1_y,
            mul_result_x,
            mul_result_y,
            scalar} ;

        let prover_2 = MockProver::run(18, &test_circuit_2, vec![]).unwrap();
        assert_eq!(prover_2.verify(), Ok(()));
    }


}