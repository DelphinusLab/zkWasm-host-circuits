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
                x: Limb::new(None, F::one()),
                y: Limb::new(None, F::one()),
            },
            default: Point {
                x: Limb::new(None, F::one()),
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
         * y3 = (y1y2 - x1x2)/(1 - lambda)
         */
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
        )?[4].clone();
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
        )?[4].clone();
        let lambda = self.config.assign_line(region, &mut (), offset,
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
        )?[4].clone();

        let x3_f = lhs.x.value * rhs.y.value + lhs.y.value * rhs.x.value;
        let x3s = self.config.assign_line(region, &mut (), offset,
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
        )?[4].clone();

        //x3 * (1+lambda) = x3s
        let x3_f = x3s.value * (F::one() + lambda.value).invert().unwrap();
        let x3 = self.config.assign_line(region, &mut (), offset,
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
        )?[3].clone();



        let y3_f = lhs.y.value * rhs.y.value - lhs.x.value * rhs.x.value;
        let y3s = self.config.assign_line(region, &mut (), offset,
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
        let y3 = self.config.assign_line(region, &mut (), offset,
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
        _region: &mut Region<F>,
        _offset: &mut usize,
        _lhs: &Limb<F>,
        _rhs: &Point<F>,
    ) -> Result<Point<F>, Error> {
        todo!()
    }

}

