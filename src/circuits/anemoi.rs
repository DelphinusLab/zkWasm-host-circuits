use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Column;

use crate::circuits::{
    CommonGateConfig,
    Limb,
};

use std::marker::PhantomData;

use halo2_proofs::{
    circuit::Region,
    plonk::{
        ConstraintSystem,
        Error
    },
};

pub const STATE_WIDTH: usize = 2;
/// 1 element of the state is reserved for rate.
pub const RATE_WIDTH: usize = 1;

/// The state is divided into two even-length rows.
pub const NUM_COLUMNS: usize = 1;

/// One element (32-bytes) is returned as digest.
pub const DIGEST_SIZE: usize = RATE_WIDTH;

/// The number of rounds is set to 21 to provide 128-bit security level.
pub const NUM_HASH_ROUNDS: usize = 21;

pub const RATE: usize = 2;

pub struct AnemoiState<F: FieldExt> {
    state: [Limb<F>; STATE_WIDTH],
    const_c: [F; NUM_HASH_ROUNDS],
    const_d: [F; NUM_HASH_ROUNDS],
    delta: F,
}

pub struct AnemoiChip<F:FieldExt> {
    pub config: CommonGateConfig,
    anemoi_state: AnemoiState<F>,
    _marker: PhantomData<F>
}

// impl chip
impl<F: FieldExt> AnemoiChip<F> {
    pub fn construct(config: CommonGateConfig, const_c: [F; NUM_HASH_ROUNDS], const_d: [F; NUM_HASH_ROUNDS], delta: F) -> Self {
        // initialized as all zeros
        let state = [0u32; STATE_WIDTH].map(|_| Limb::new(None, F::zero()));
        let state = AnemoiState {
            state: state,
            const_c: const_c,
            const_d: const_d,
            delta: delta,
        };

        AnemoiChip {
            config,
            anemoi_state: state,
            _marker: PhantomData,
        }
    }

    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.anemoi_state.initialize(config, region, offset)?;

        Ok(())
    }

    pub fn configure(cs: &mut ConstraintSystem<F>, shared_advices: &Vec<Column<Advice>>) -> CommonGateConfig {
        CommonGateConfig::configure(cs, &(), shared_advices)
    }

    pub fn hash(
        &mut self,
        region: &mut Region<F>,
        offset: &mut usize,
        inputs: &[Limb<F>; RATE], 
        result: &Limb<F>,
    ) -> Result<(), Error> {
        let vals = inputs.clone().map(|x| Some(x));
        let mut vals = vals.to_vec();
        vals.push(None);
        vals.push(None);
        vals.push(None);
        let in_data = self.config.assign_witness(
            region,
            &mut (),
            offset,
            vals.try_into().unwrap(),
            0,
        )?;
        for ip in in_data {
            self.anemoi_state.read_input(&self.config, region, offset,&ip.clone())?;
            self.anemoi_state.apply_permutation(&self.config, region, offset)?;
        };

        // check result
        assert!(self.anemoi_state.state[0].value == result.value);
        Ok(())
    }
}

// impl state
impl<F: FieldExt> AnemoiState<F>{
    pub fn initialize(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        let zero = config.assign_constant(region, &mut (), offset, &F::zero())?;
        let state = [0u32;STATE_WIDTH].map(|_| zero.clone());  // initialize as all zeros
        self.state = state;

        Ok(())
    }

    pub fn apply_sbox_layer(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error>{
        // initialize x and y by spliting original state into two
        // need to copy cell over, let's use select
        let mut x: [Limb<F>; NUM_COLUMNS] = [0u32; NUM_COLUMNS].map(|_| Limb::new(None, F::zero()));
        let mut y: [Limb<F>; NUM_COLUMNS] = [0u32; NUM_COLUMNS].map(|_| Limb::new(None, F::zero()));
        let mut t: [Limb<F>; NUM_COLUMNS] = [0u32; NUM_COLUMNS].map(|_| Limb::new(None, F::zero()));


        // copy first half of state into x, 2nd half into y
        x[0] = config.select(region, &mut (), offset, &Limb::new(None, F::zero()), &self.state[0].clone(), &Limb::new(None, F::zero()), 0)?;
        y[0] = config.select(region, &mut (), offset, &Limb::new(None, F::zero()), &self.state[1].clone(), &Limb::new(None, F::zero()), 0)?;

        for i in 0..NUM_COLUMNS {
            let y_square = self.mul(config, region, offset, &y[i].clone(), &y[i].clone())?;
            let g_y_square = self.mul_by_generator(config, region, offset, &y_square.clone())?;
            let xi = x[i].clone().value - g_y_square.clone().value;
            let xi_f = config.assign_line(region, &mut (), offset, 
                [
                Some(x[i].clone()),
                Some(Limb::new(None, xi)),
                Some(g_y_square.clone()),
                None, 
                None,
                None
                ], 
                [Some(F::one()), Some(-F::one()), Some(-F::one()), None, None, None, None, None, None], 
                0,
            )?[1].clone();
            x[i] = xi_f;
        }

        for i in 0..NUM_COLUMNS {
            let xi_inv_alpha = self.exp_inv_alpha(config, region, offset, &x[i].clone())?;
            t[i] = xi_inv_alpha;
        }

        // compute y after sbox
        for i in 0..NUM_COLUMNS {
            let yi = y[i].value.clone() - t[i].clone().value;
            let yi_f = config.assign_line( region, &mut (), offset, 
                [
                Some(y[i].clone()),
                Some(Limb::new(None, yi)),
                Some(t[i].clone()),
                None, 
                None,
                None
                ],
                [Some(F::one()), Some(-F::one()), Some(-F::one()), None, None, None, None, None, None], 
                0,
            )?[1].clone();
            y[i] = yi_f;
        }

        // compute x after sbox
        for i in 0..NUM_COLUMNS {
            let yi_square = self.mul(config, region, offset, &y[i].clone(), &y[i].clone())?;
            let g_yi_square = self.mul_by_generator(config, region, offset, &yi_square.clone())?;
            let xi_t = x[i].clone().value + g_yi_square.clone().value;
            let xi_f = config.assign_line( region, &mut (), offset, 
                [
                Some(x[i].clone()),
                Some(Limb::new(None, xi_t)),
                Some(g_yi_square.clone()),
                None, 
                None,
                None
                ],
                [Some(F::one()), Some(-F::one()), Some(F::one()), None, None, None, None, None, None], 
                0,
            )?[1].clone();
            let xi_s = self.add(config, region, offset, &xi_f.clone(), &Limb::new(None, self.delta))?;

            x[i] = xi_s;
            *offset += 1;
        }
        
        // need a constrain here
        self.state[0] = x[0].clone();
        self.state[1] = y[0].clone();


        Ok(())
    }
    
    pub fn apply_linear_layer(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
    ) -> Result<(), Error>{
        self.state[1] = self.add(config, region, offset, &self.state[1].clone(), &self.state[0].clone())?;
        self.state[0] = self.add(config, region, offset, &self.state[0].clone(), &self.state[1].clone())?;
        
        Ok(())
    }
    
    pub fn apply_round(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize, 
        step: usize
    )  -> Result<(), Error> {
        self.state[0] = self.add(config, region, offset, &self.state[0].clone(), &Limb::new(None, self.const_c[step % NUM_HASH_ROUNDS].clone()))?;
        self.state[1] = self.add(config, region, offset, &self.state[1].clone(), &Limb::new(None, self.const_d[step % NUM_HASH_ROUNDS].clone()))?;
 
        self.apply_linear_layer(config, region, offset)?;
        self.apply_sbox_layer(config, region, offset)?;

        Ok(())
    }

    pub fn add_constant_one(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize, 
    ) -> Result<(), Error> {
        self.state[STATE_WIDTH-1] = self.add(config, region, offset, &self.state[STATE_WIDTH-1].clone(), &Limb::new(None, F::one()))?;
        Ok(())
    }

    pub fn read_input(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize, 
        input: &Limb<F>, 
    ) -> Result<(), Error> {
        self.state[0] = self.add(config, region, offset, &self.state[0].clone(), &input.clone())?;

        Ok(())
    }

    pub fn apply_permutation(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize, 
    ) -> Result<(), Error> {

        for i in 0..NUM_HASH_ROUNDS {
            self.apply_round(config, region, offset, i)?;
        }
    
        self.apply_linear_layer(config, region, offset)?;

        Ok(())
    }

    pub fn add(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        a: &Limb<F>, 
        b: &Limb<F>
    ) -> Result<Limb<F>, Error>{
        let rhs_f = a.clone().value + b.clone().value;
        let rhs = config.assign_line(region, &mut (), offset,
            [
                Some(a.clone()),
                Some(b.clone()),
                None,
                Some(Limb::new(None, rhs_f.clone())),
                None,
                None,
            ],
            [Some(F::one()), Some(F::one()), None, Some(-F::one()), None, None, None, None, None],
            0
        )?[2].clone();

        Ok(rhs)
    }

    // alpha_inv is a known value so we just perform necessary multiplications and call it many times
    // got this fn from https://github.com/anemoi-hash/anemoi-rust/blob/main/src/bn_254/sbox.rs by anemoi team
    pub fn exp_inv_alpha(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        x: &Limb<F>, 
    ) -> Result<Limb<F>, Error> {
        let t14 = self.mul(config, region, offset, &x.clone(), &x.clone())?; //          1: 2
        let t2 = self.mul(config, region, offset, &t14.clone(), &x.clone())?; //         2: 3
        let t1 = self.mul(config, region, offset, &t14.clone(), &t14.clone())?; //       3: 4
        let t0 = self.mul(config, region, offset, &t2.clone(), &t14.clone())?; //        4: 5
        let t2 = self.mul(config, region, offset, &t2.clone(), &t2.clone())?; //         5: 6
        let t13 = self.mul(config, region, offset, &t1.clone(), &t1.clone())?; //        6: 8
        let t1 = self.mul(config, region, offset, &t0.clone(), &t1.clone())?; //         7: 9
        let t6 = self.mul(config, region, offset, &t13.clone(), &t0.clone())?; //        8: 13
        let t0 = self.mul(config, region, offset, &t13.clone(), &t2.clone())?; //       9: 14
        let t12 = self.mul(config, region, offset, &t13.clone(), &t13.clone())?; //      10: 16
        let t8 = self.mul(config, region, offset, &t6.clone(), &t1.clone())?; //         11: 22
        let t3 = self.mul(config, region, offset, &t6.clone(), &t6.clone())?; //         12: 26
        let t15 = self.mul(config, region, offset, &t12.clone(), &t0.clone())?;//        13: 30
        let t4 = self.mul(config, region, offset, &t8.clone(), &t1.clone())?; //         14: 31
        let t9 = self.mul(config, region, offset, &t3.clone(), &t12.clone())?; //        15: 42
        let t20 = self.mul(config, region, offset, &t4.clone(), &t0.clone())?; //        16: 45
        let t3 = self.mul(config, region, offset, &t4.clone(), &t8.clone())?; //         17: 53
        let t5 = self.mul(config, region, offset, &t4.clone(), &t4.clone())?; //         18: 62
        let t7 = self.mul(config, region, offset, &t20.clone(), &t8.clone())?; //        19: 67
        let t10 = self.mul(config, region, offset, &t3.clone(), &t12.clone())?; //       20: 69
        let t18 = self.mul(config, region, offset, &t9.clone(), &t4.clone())?;//         21: 73
        let t3 = self.mul(config, region, offset, &t10.clone(), &t6.clone())?; //        22: 82
        let t11 = self.mul(config, region, offset, &t18.clone(), &t5.clone())?; //       23: 135
        let t21 = self.mul(config, region, offset, &t11.clone(), &t15.clone())?;//       24: 165
        let t16 = self.mul(config, region, offset, &t21.clone(), &t12.clone())?; //      25: 181
        let t12 = self.mul(config, region, offset, &t21.clone(), &t9.clone())?; //       26: 207
        let t14 = self.mul(config, region, offset, &t12.clone(), &t14.clone())?; //      27: 209
        let t15 = self.mul(config, region, offset, &t12.clone(), &t2.clone())?; //       28: 213
        let t2 = self.mul(config, region, offset, &t21.clone(), &t3.clone())?; //        29: 247
        let t5 = self.mul(config, region, offset, &t2.clone(), &t5.clone())?; //         30: 309
        let t19 = self.mul(config, region, offset, &t5.clone(), &t13.clone())?; //       31: 317
        let t3 = self.mul(config, region, offset, &t19.clone(), &t3.clone())?; //        32: 399
        let t17 = self.mul(config, region, offset, &t3.clone(), &t9.clone())?; //        33: 441
        let t9 = self.mul(config, region, offset, &t17.clone(), &t0.clone())?; //        34: 455
        let t8 = self.mul(config, region, offset, &t9.clone(), &t8.clone())?; //         35: 477
        let t13 = self.mul(config, region, offset, &t8.clone(), &t0.clone())?; //        36: 491
        let mut t0 = self.mul(config, region, offset, &t5.clone(), &t5.clone())?; //     37: 618
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         38: 1236
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         39: 2472
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         40: 4944
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         41: 9888
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         42: 19776
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        43: 39552
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         44: 79104
        t0 = self.mul(config, region, offset, &t0.clone(), &t16.clone())?; //       45: 79285
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         46: 158570
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         47: 317140
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         48: 634280
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         49: 1268560
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         50: 2537120
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         51: 5074240
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         52: 10148480
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         53: 20296960
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         54: 40593920
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         55: 81187840
        t0 = self.mul(config, region, offset, &t0.clone(), &t21.clone())?; //        56: 81188005
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         57: 162376010
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         58: 324752020
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         59: 649504040
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         60: 1299008080
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         61: 2598016160
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         62: 5196032320
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         63: 10392064640
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         64: 20784129280
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         65: 41568258560
        t0 = self.mul(config, region, offset, &t0.clone(), &t20.clone())?; //        66: 41568258605
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         67: 83136517210
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         68: 166273034420
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         69: 332546068840
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         70: 665092137680
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         71: 1330184275360
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         72: 2660368550720
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         73: 5320737101440
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         74: 10641474202880
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         75: 21282948405760
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         76: 42565896811520
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         77: 85131793623040
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         78: 170263587246080
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         79: 340527174492160
        t0 = self.mul(config, region, offset, &t0.clone(), &t19.clone())?; //        80: 340527174492477
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         81: 681054348984954
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         82: 1362108697969908
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         83: 2724217395939816
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         84: 5448434791879632
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         85: 10896869583759264
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         86: 21793739167518528
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         87: 43587478335037056
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         88: 87174956670074112
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         89: 174349913340148224
        t0 = self.mul(config, region, offset, &t0.clone(), &t5.clone())?; //                 90: 174349913340148533
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         91: 348699826680297066
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         92: 697399653360594132
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         93: 1394799306721188264
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         94: 2789598613442376528
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         95: 5579197226884753056
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         96: 11158394453769506112
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         97: 22316788907539012224
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //         98: 44633577815078024448
        t0 = self.mul(config, region, offset, &t0.clone(), &t18.clone())?; //        99: 44633577815078024521
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        100: 89267155630156049042
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        101: 178534311260312098084
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        102: 357068622520624196168
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        103: 714137245041248392336
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        104: 1428274490082496784672
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        105: 2856548980164993569344
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        106: 5713097960329987138688
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        107: 11426195920659974277376
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        108: 22852391841319948554752
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        109: 45704783682639897109504
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        110: 91409567365279794219008
        t0 = self.mul(config, region, offset, &t0.clone(), &t17.clone())?; //       111: 91409567365279794219449
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        112: 182819134730559588438898
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        113: 365638269461119176877796
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        114: 731276538922238353755592
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        115: 1462553077844476707511184
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        116: 2925106155688953415022368
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        117: 5850212311377906830044736
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        118: 11700424622755813660089472
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        119: 23400849245511627320178944
        t0 = self.mul(config, region, offset, &t0.clone(), &t16.clone())?; //       120: 23400849245511627320179125
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        121: 46801698491023254640358250
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        122: 93603396982046509280716500
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        123: 187206793964093018561433000
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        124: 374413587928186037122866000
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        125: 748827175856372074245732000
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        126: 1497654351712744148491464000
        t0 = self.mul(config, region, offset, &t0.clone(), &t4.clone())?; //        127: 1497654351712744148491464031
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        128: 2995308703425488296982928062
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        129: 5990617406850976593965856124
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        130: 11981234813701953187931712248
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        131: 23962469627403906375863424496
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        132: 47924939254807812751726848992
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        133: 95849878509615625503453697984
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        134: 191699757019231251006907395968
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        135: 383399514038462502013814791936
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        136: 766799028076925004027629583872
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        137: 1533598056153850008055259167744
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        138: 3067196112307700016110518335488
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        139: 6134392224615400032221036670976
        t0 = self.mul(config, region, offset, &t0.clone(), &t12.clone())?; //       140: 6134392224615400032221036671183
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        141: 12268784449230800064442073342366
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        142: 24537568898461600128884146684732
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        143: 49075137796923200257768293369464
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        144: 98150275593846400515536586738928
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        145: 196300551187692801031073173477856
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        146: 392601102375385602062146346955712
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        147: 785202204750771204124292693911424
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        148: 1570404409501542408248585387822848
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        149: 3140808819003084816497170775645696
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        150: 6281617638006169632994341551291392
        t0 = self.mul(config, region, offset, &t0.clone(), &t15.clone())?; //       151: 6281617638006169632994341551291605
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        152: 12563235276012339265988683102583210
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        153: 25126470552024678531977366205166420
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        154: 50252941104049357063954732410332840
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        155: 100505882208098714127909464820665680
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        156: 201011764416197428255818929641331360
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        157: 402023528832394856511637859282662720
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        158: 804047057664789713023275718565325440
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        159: 1608094115329579426046551437130650880
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        160: 3216188230659158852093102874261301760
        t0 = self.mul(config, region, offset, &t0.clone(), &t14.clone())?; //       161: 3216188230659158852093102874261301969
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        162: 6432376461318317704186205748522603938
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        163: 12864752922636635408372411497045207876
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        164: 25729505845273270816744822994090415752
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        165: 51459011690546541633489645988180831504
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        166: 102918023381093083266979291976361663008
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        167: 205836046762186166533958583952723326016
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        168: 411672093524372333067917167905446652032
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        169: 823344187048744666135834335810893304064
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        170: 1646688374097489332271668671621786608128
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        171: 3293376748194978664543337343243573216256
        t0 = self.mul(config, region, offset, &t0.clone(), &t13.clone())?; //       172: 3293376748194978664543337343243573216747
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        173: 6586753496389957329086674686487146433494
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        174: 13173506992779914658173349372974292866988
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        175: 26347013985559829316346698745948585733976
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        176: 52694027971119658632693397491897171467952
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        177: 105388055942239317265386794983794342935904
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        178: 210776111884478634530773589967588685871808
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        179: 421552223768957269061547179935177371743616
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        180: 843104447537914538123094359870354743487232
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        181: 1686208895075829076246188719740709486974464
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        182: 3372417790151658152492377439481418973948928
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        183: 6744835580303316304984754878962837947897856
        t0 = self.mul(config, region, offset, &t0.clone(), &t12.clone())?; //       184: 6744835580303316304984754878962837947898063
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        185: 13489671160606632609969509757925675895796126
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        186: 26979342321213265219939019515851351791592252
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        187: 53958684642426530439878039031702703583184504
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        188: 107917369284853060879756078063405407166369008
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        189: 215834738569706121759512156126810814332738016
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        190: 431669477139412243519024312253621628665476032
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        191: 863338954278824487038048624507243257330952064
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        192: 1726677908557648974076097249014486514661904128
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        193: 3453355817115297948152194498028973029323808256
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        194: 6906711634230595896304388996057946058647616512
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        195: 13813423268461191792608777992115892117295233024
        t0 = self.mul(config, region, offset, &t0.clone(), &t11.clone())?; //            196: 13813423268461191792608777992115892117295233159
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        197: 27626846536922383585217555984231784234590466318
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        198: 55253693073844767170435111968463568469180932636
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        199: 110507386147689534340870223936927136938361865272
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        200: 221014772295379068681740447873854273876723730544
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        201: 442029544590758137363480895747708547753447461088
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        202: 884059089181516274726961791495417095506894922176
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        203: 1768118178363032549453923582990834191013789844352
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        204: 3536236356726065098907847165981668382027579688704
        t0 = self.mul(config, region, offset, &t0.clone(), &t10.clone())?; //            205: 3536236356726065098907847165981668382027579688773
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        206: 7072472713452130197815694331963336764055159377546
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        207: 14144945426904260395631388663926673528110318755092
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        208: 28289890853808520791262777327853347056220637510184
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        209: 56579781707617041582525554655706694112441275020368
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        210: 113159563415234083165051109311413388224882550040736
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        211: 226319126830468166330102218622826776449765100081472
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        212: 452638253660936332660204437245653552899530200162944
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        213: 905276507321872665320408874491307105799060400325888
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        214: 1810553014643745330640817748982614211598120800651776
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        215: 3621106029287490661281635497965228423196241601303552
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        216: 7242212058574981322563270995930456846392483202607104
        t0 = self.mul(config, region, offset, &t0.clone(), &t9.clone())?; //             217: 7242212058574981322563270995930456846392483202607559
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        218: 14484424117149962645126541991860913692784966405215118
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        219: 28968848234299925290253083983721827385569932810430236
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        220: 57937696468599850580506167967443654771139865620860472
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        221: 115875392937199701161012335934887309542279731241720944
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        222: 231750785874399402322024671869774619084559462483441888
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        223: 463501571748798804644049343739549238169118924966883776
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        224: 927003143497597609288098687479098476338237849933767552
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        225: 1854006286995195218576197374958196952676475699867535104
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        226: 3708012573990390437152394749916393905352951399735070208
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        227: 7416025147980780874304789499832787810705902799470140416
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        228: 14832050295961561748609578999665575621411805598940280832
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        229: 29664100591923123497219157999331151242823611197880561664
        t0 = self.mul(config, region, offset, &t0.clone(), &t8.clone())?; //        230: 29664100591923123497219157999331151242823611197880562141
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        231: 59328201183846246994438315998662302485647222395761124282
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        232: 118656402367692493988876631997324604971294444791522248564
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        233: 237312804735384987977753263994649209942588889583044497128
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        234: 474625609470769975955506527989298419885177779166088994256
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        235: 949251218941539951911013055978596839770355558332177988512
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        236: 1898502437883079903822026111957193679540711116664355977024
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        237: 3797004875766159807644052223914387359081422233328711954048
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        238: 7594009751532319615288104447828774718162844466657423908096
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        239: 15188019503064639230576208895657549436325688933314847816192
        t0 = self.mul(config, region, offset, &t0.clone(), &t7.clone())?; //        240: 15188019503064639230576208895657549436325688933314847816259
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        241: 30376039006129278461152417791315098872651377866629695632518
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        242: 60752078012258556922304835582630197745302755733259391265036
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        243: 121504156024517113844609671165260395490605511466518782530072
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        244: 243008312049034227689219342330520790981211022933037565060144
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        245: 486016624098068455378438684661041581962422045866075130120288
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        246: 972033248196136910756877369322083163924844091732150260240576
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        247: 1944066496392273821513754738644166327849688183464300520481152
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        248: 3888132992784547643027509477288332655699376366928601040962304
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        249: 7776265985569095286055018954576665311398752733857202081924608
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        250: 15552531971138190572110037909153330622797505467714404163849216
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        251: 31105063942276381144220075818306661245595010935428808327698432
        t0 = self.mul(config, region, offset, &t0.clone(), &t6.clone())?; //        252: 31105063942276381144220075818306661245595010935428808327698445
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        253: 62210127884552762288440151636613322491190021870857616655396890
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        254: 124420255769105524576880303273226644982380043741715233310793780
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        255: 248840511538211049153760606546453289964760087483430466621587560
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        256: 497681023076422098307521213092906579929520174966860933243175120
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        257: 995362046152844196615042426185813159859040349933721866486350240
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        258: 1990724092305688393230084852371626319718080699867443732972700480
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        259: 3981448184611376786460169704743252639436161399734887465945400960
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        260: 7962896369222753572920339409486505278872322799469774931890801920
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        261: 15925792738445507145840678818973010557744645598939549863781603840
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        262: 31851585476891014291681357637946021115489291197879099727563207680
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        263: 63703170953782028583362715275892042230978582395758199455126415360
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        264: 127406341907564057166725430551784084461957164791516398910252830720
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        265: 254812683815128114333450861103568168923914329583032797820505661440
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        266: 509625367630256228666901722207136337847828659166065595641011322880
        t0 = self.mul(config, region, offset, &t0.clone(), &t5.clone())?; //        267: 509625367630256228666901722207136337847828659166065595641011323189
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        268: 1019250735260512457333803444414272675695657318332131191282022646378
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        269: 2038501470521024914667606888828545351391314636664262382564045292756
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        270: 4077002941042049829335213777657090702782629273328524765128090585512
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        271: 8154005882084099658670427555314181405565258546657049530256181171024
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        272: 16308011764168199317340855110628362811130517093314099060512362342048
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        273: 32616023528336398634681710221256725622261034186628198121024724684096
        t0 = self.mul(config, region, offset, &t0.clone(), &t4.clone())?; //        274: 32616023528336398634681710221256725622261034186628198121024724684127
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        275: 65232047056672797269363420442513451244522068373256396242049449368254
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        276: 130464094113345594538726840885026902489044136746512792484098898736508
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        277: 260928188226691189077453681770053804978088273493025584968197797473016
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        278: 521856376453382378154907363540107609956176546986051169936395594946032
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        279: 1043712752906764756309814727080215219912353093972102339872791189892064
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        280: 2087425505813529512619629454160430439824706187944204679745582379784128
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        281: 4174851011627059025239258908320860879649412375888409359491164759568256
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        282: 8349702023254118050478517816641721759298824751776818718982329519136512
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        283: 16699404046508236100957035633283443518597649503553637437964659038273024
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        284: 33398808093016472201914071266566887037195299007107274875929318076546048
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        285: 66797616186032944403828142533133774074390598014214549751858636153092096
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        286: 133595232372065888807656285066267548148781196028429099503717272306184192
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        287: 267190464744131777615312570132535096297562392056858199007434544612368384
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        288: 534380929488263555230625140265070192595124784113716398014869089224736768
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        289: 1068761858976527110461250280530140385190249568227432796029738178449473536
        t0 = self.mul(config, region, offset, &t0.clone(), &t3.clone())?; //        290: 1068761858976527110461250280530140385190249568227432796029738178449473935
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        291: 2137523717953054220922500561060280770380499136454865592059476356898947870
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        292: 4275047435906108441845001122120561540760998272909731184118952713797895740
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        293: 8550094871812216883690002244241123081521996545819462368237905427595791480
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        294: 17100189743624433767380004488482246163043993091638924736475810855191582960
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        295: 34200379487248867534760008976964492326087986183277849472951621710383165920
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        296: 68400758974497735069520017953928984652175972366555698945903243420766331840
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        297: 136801517948995470139040035907857969304351944733111397891806486841532663680
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        298: 273603035897990940278080071815715938608703889466222795783612973683065327360
        t0 = self.mul(config, region, offset, &t0.clone(), &t2.clone())?; //        299: 273603035897990940278080071815715938608703889466222795783612973683065327607
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        300: 547206071795981880556160143631431877217407778932445591567225947366130655214
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        301: 1094412143591963761112320287262863754434815557864891183134451894732261310428
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        302: 2188824287183927522224640574525727508869631115729782366268903789464522620856
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        303: 4377648574367855044449281149051455017739262231459564732537807578929045241712
        t0 = self.mul(config, region, offset, &t0.clone(), &t0.clone())?; //        304: 8755297148735710088898562298102910035478524462919129465075615157858090483424
        t0 = self.mul(config, region, offset, &t0.clone(), &t1.clone())?; //        305: 8755297148735710088898562298102910035478524462919129465075615157858090483433

        Ok(t0)
    }

    fn mul(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        a: &Limb<F>,
        b: &Limb<F>
    ) -> Result<Limb<F>, Error> {
        let result_t = a.clone().value * b.clone().value;
        let result_f = config.assign_line(region, &mut (), offset, 
        [
            Some(a.clone()),
            Some(Limb::new(None, result_t)),
            None,
            Some(b.clone()),
            None,
            None,
        ], 
        [None, Some(-F::one()), None, None, None, None, Some(F::one()), None, None], 
        0
        )?[1].clone();
        *offset += 1;

        Ok(result_f)
    }

    // generator of Fq is 3
    fn mul_by_generator(
        &mut self,
        config: &CommonGateConfig,
        region: &mut Region<F>,
        offset: &mut usize,
        x: &Limb<F>, 
    ) -> Result<Limb<F>, Error> {
        let x2_f = x.value.clone() + x.value.clone() + x.value.clone();
        let rhs = config.assign_line(region, &mut (), offset,
        [
            Some(x.clone()),
            Some(x.clone()),
            Some(x.clone()),
            Some(Limb::new(None, x2_f.clone())),
            None,
            None,
        ],
        [Some(F::one()), Some(F::one()), Some(F::one()), Some(-F::one()), None, None, None, None, None],
        0
        )?[3].clone();
        *offset += 1;
        Ok(rhs)
    }

}


// test
#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fq as Felt;
    use halo2_proofs::dev::MockProver;

    use crate::circuits::CommonGateConfig;
    use crate::value_for_assign;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        Limb,
        AnemoiChip,
        NUM_HASH_ROUNDS, 
        RATE,
    };


    // CONSTANTS
    // ================================================================================================

    const C: [Felt; NUM_HASH_ROUNDS] = [
    Felt::from_raw([
        0x0000000000000023,
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000, // converted
    ]), // should be 35
    Felt::from_raw([
        0x775b1f206923c47d,
        0xa8f87a7963284fbb,
        0x3bae816d61d6132a,
        0xdeaee26fa771e0b, // converted
    ]),
    Felt::from_raw([
        0x22a976e6d07d60f5,
        0xc34df41e5fe46ab6,
        0x260d3da3fedf84b,
        0x2f4c8ca1724196cf, // converted
    ]),
    Felt::from_raw([
        0xc30db64d510ee564,
        0x95744059950b323d,
        0x650e5c6bd5cfcb3e,
        0x5d30d8a084ddd31,  // converted
    ]),
    Felt::from_raw([
        0xcd05768f1b651e71,
        0xad09e76646f8fc45,
        0xdad4ecd80712fe07,
        0x21d0c94592289e73, // converted
    ]),
    Felt::from_raw([
        0xeee4a5b31c720775,
        0xe685edbf1f0f875e,
        0xecda8089d8eb9a3d,
        0xad405df9e60b24e,  // converted 5
    ]),
    Felt::from_raw([
        0x37019677c912b86e,
        0xf1b16555957afe6c,
        0x3631c2568a36f711,
        0xcc03a758b72c918, // converted
    ]),
    Felt::from_raw([
        0x433a8db6250f1315,
        0x16c912d5d9d4ed48,
        0x7d7c67b60ccdf98d,
        0xbc1b9119e2f8d32,  // converted
    ]),
    Felt::from_raw([
        0x46cb1f57666d0206,
        0x8a58a8f27efdb933,
        0x83e8dd8a41625cd6,
        0xfdefd9a0f81cc28,  // converted
    ]),
    Felt::from_raw([
        0x8add6292e2e1e661,
        0xf1f53531867319e8,
        0x3d6fcf9e000ccbcd,
        0x545268f14d1ef2d,  // converted
    ]),
    Felt::from_raw([
        0xa2def1f14b524aae,
        0x275d597192211146,
        0xa42c1f3e6a1f7e3b,
        0x304083d89066c255, // converted 10
    ]),
    Felt::from_raw([
        0x250db07064b2c906,
        0x1b6b4eeb73bd34db,
        0x33427c42db863ba9,
        0x2f6c68f4f14399a4, // converted
    ]),
    Felt::from_raw([
        0xc316649d3fc3381d,
        0xc0454a7c949fa493,
        0xafc8f158a8e78784,
        0x2c253abeaa8f1309, // converted
    ]),
    Felt::from_raw([
        0x28ee11171ca3660e,
        0xeb197941a15815a9,
        0xd6329fa5a982a43,
        0x28a62c2fcdf31601, // converted
    ]),
    Felt::from_raw([
        0x4e0f7d84e1129058,
        0x940999a2a073a089,
        0xcceab807358a652f,
        0xb8c0b1fdb7e110a,  // converted
    ]),
    Felt::from_raw([
        0x70cf039d739d1046,
        0xf569e914e8d94eee,
        0xfb255b7fde25b695,
        0x1468c3253afd5301, // converted 15
    ]),
    Felt::from_raw([
        0x3d2a365c3b57cd1b,
        0x4312821f06af1a11,
        0xd30bc6c4014eb88e,
        0x76505a8aac3ed67, // converted
    ]),
    Felt::from_raw([
        0x671b73192354638f,
        0x7001d04e2195dd2,
        0xfaeb9a1e631fc8f5,
        0x1989a97904a6cc74, // converted
    ]),
    Felt::from_raw([
        0xf1e8b99b2fe59e14,
        0x6c3bcc9fa9f0c3ee,
        0x7fb680e63a8b45a4,
        0xcc2035b47d9bb9e,  // converted
    ]),
    Felt::from_raw([
        0xe55901d82eafa11d,
        0x38694ed7495dc378,
        0x85acb7120a4ca071,
        0x218d252816b694c5, // converted
    ]),
    Felt::from_raw([
        0x7b2bfc5a6086dccd,
        0x2a44cbfa06667305,
        0xa335ab84fa3fd829,
        0xf083607ff8712f6,  // converted 20
    ]),
    ];

    /// Additive round constants D for Anemoi.
    const D: [Felt; NUM_HASH_ROUNDS] = [
        Felt::from_raw([
            0xd2c05d64905353a8,
            0xba56470b9af68708,
            0xd03583cf0100e593,
            0x2042def740cbc01b,
        ]),
        Felt::from_raw([
            0x73a2fbd4019568b4,
            0x5cb6796c004a370d,
            0xbdd497eaca1967df,
            0x20e95d0e6735f19a,
        ]),
        Felt::from_raw([
            0xee681bf532a91923,
            0x8385c5e9d09c9ee3,
            0x4072d35cf31e5204,
            0x2b6b3836e5247620,
        ]),
        Felt::from_raw([
            0xf48fc0aaaaad418a,
            0xf9a5f194fb14170a,
            0x5fe8df694a1bfe5c,
            0x3f3ec435fea59d9,
        ]),
        Felt::from_raw([
            0xe014fffb8fc1f126,
            0x350043a3cf4f64c8,
            0x2afd01afa94add8c,
            0xe760bbfd4bc5260,
        ]),
        Felt::from_raw([
            0x15162795759ef68,
            0x1727676991bd7352,
            0x5f43de4dc2cd5c9c,
            0x148baca8bb5a730c,   // 5
        ]),
        Felt::from_raw([
            0x7aad2edb101c1926,
            0xd96956877d2d5b4b,
            0x17a23a1d8b446506,
            0x2dac0dc7fef687d7,
        ]),
        Felt::from_raw([
            0x2fef6d8c3c4c4457,
            0x8464595c1a04bf97,
            0xeaff4b1dc220b4c3,
            0x239dc36bdce081cf,
        ]),
        Felt::from_raw([
            0x8999c35c997fb84e,
            0x64dadc90d848b6c9,
            0xe87539e33456eeeb,
            0x293f0565a6c6611c,
        ]),
        Felt::from_raw([
            0xe7e351515eaddd87,
            0xa9eaebd37ecda9ba,
            0x278f2326549a3427,
            0x1ba459601d9c6c78,
        ]),
        Felt::from_raw([
            0x55f14c562a9a9308,
            0xd5c8c8fd76fab00b,
            0x6feeb1125758e33b,
            0x23f26cea6945ec15,         // 10
        ]),
        Felt::from_raw([
            0xe1342a430bee2f41,
            0xb3f8b199ef4d013d,
            0x6a9548ebb41718dc,
            0xbac5daffbafcd13,
        ]),
        Felt::from_raw([
            0x2aeef4a67c235b35,
            0xd9977df9611952df,
            0xb95fbb84b009d6be,
            0x184e80dc14df31ee,
        ]),
        Felt::from_raw([
            0x968b0e12479b11c9,
            0x4f7050525593443a,
            0x4881803e03833ab5,
            0x2a9075fbd6deb7d8,
        ]),
        Felt::from_raw([
            0xdfcd056b4a53c1d7,
            0xef8833b711fc7e09,
            0x495ec0abfeea5d19,
            0x170c18b10ac6cccf,
        ]),
        Felt::from_raw([
            0x23398e1996ad0ff8,
            0xf5b7bae9cc1d59bb,
            0x6612bce50cb34e4d,
            0x395e21f8759fb40,          // 15
        ]),
        Felt::from_raw([
            0xd623a49CAB9C1525,
            0xF9CDE1D0F3A45A16,
            0x6074C20FA3EB065E,
            0x00AC9DA9488ECDFB,
        ]),
        Felt::from_raw([
            0xfe19c069491f78ba,
            0x5aa95dc039eb7f8a,
            0x190f717dfd1a2a1c,
            0x24fae1a08a518137,
        ]),
        Felt::from_raw([
            0x5c3ac9fb10b98b6c,
            0x78709792f130f84b,
            0xaba2e0fff5246b1c,
            0x3428dc08c3b8b36,
        ]),
        Felt::from_raw([
            0x96e4cea20b00019d,
            0x7f47df444750efae,
            0x4accf8d91870397b,
            0x2d2a504d0f8d8c1e,
        ]),
        Felt::from_raw([
            0xe68abccf2b3601a8,
            0x8dc73527bccb9ec2,
            0xd126f57ec2b39998,
            0x2ef503c0bb8962e7,
        ]),
    ];

    /// Exponent of the Anemoi S-Box
    #[allow(unused)]
    const ALPHA: u32 = 5;

    #[allow(unused)]
    /// Inverse exponent
    const INV_ALPHA: [u64; 4] = [
        0x180d04d5f031fee9,
        0xd633c43a29c71dd2,
        0x49b9b57c33cd568b,
        0x135b52945a13d9aa,
    ];

    #[allow(unused)]
    /// Multiplier of the Anemoi S-Box
    const BETA: u32 = 3;

    /// First added constant of the Anemoi S-Box
    const DELTA: Felt = Felt::from_raw(
        [0xd2c05d6490535385,
        0xba56470b9af68708,
        0xd03583cf0100e593,
        0x2042def740cbc01b,
    ]);

    // test circuit
    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    #[derive(Clone, Debug)]
    pub struct HelperChip {
        config: HelperChipConfig
    }

    impl Chip<Felt> for HelperChip {
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

        fn configure(cs: &mut ConstraintSystem<Felt>) -> HelperChipConfig {
            let limb= cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_inputs(
            &self,
            region: &mut Region<Felt>,
            offset: &mut usize,
            inputs: &[Felt; RATE],
        ) -> Result<[Limb<Felt>; RATE], Error> {
            let r = inputs.map(|x| {
                let c = region.assign_advice(
                    || format!("assign input"),
                    self.config.limb,
                    *offset,
                    || value_for_assign!(x.clone())
                ).unwrap();
                *offset += 1;
                Limb::new(Some(c), x.clone())
            });
            Ok(r)
        }


        fn assign_result(
            &self,
            region: &mut Region<Felt>,
            offset: &mut usize,
            result: &Felt,
        ) -> Result<Limb<Felt>, Error> {
            let c = region.assign_advice(
                || format!("assign result"),
                self.config.limb,
                *offset,
                || value_for_assign!(result.clone())
            )?;
            *offset += 1;
            Ok(Limb::new(Some(c), result.clone()))
        }

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
        inputs: Vec<Felt>,
        result: Felt,
    }

    #[derive(Clone, Debug)]
    struct TestConfig {
        anemoiconfig: CommonGateConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Felt> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(cs: &mut ConstraintSystem<Felt>) -> Self::Config {
            let witness = vec![
                cs.advice_column(),
                cs.advice_column(),
                cs.advice_column(),
                cs.advice_column(),
                cs.advice_column(),
            ];
            Self::Config {
               anemoiconfig: AnemoiChip::<Felt>::configure(cs, &witness),
               helperconfig: HelperChip::configure(cs),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Felt>,
        ) -> Result<(), Error> {
            let mut anemoichip = AnemoiChip::<Felt>::construct(config.clone().anemoiconfig, C, D, DELTA);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "assign anemoi test",
                |mut region| {
                    let mut offset = 0;
                    let result = helperchip.assign_result(&mut region, &mut offset, &self.result)?;
                    let input = helperchip.assign_inputs(&mut region, &mut offset, &self.inputs.clone().try_into().unwrap())?;
                    offset = 0;
                    anemoichip.anemoi_state.initialize(&config.anemoiconfig, &mut region, &mut offset)?;    // init to all zeros
                    anemoichip.hash(
                        &mut region,
                        &mut offset,
                        &input,
                        &result,
                    )?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_anemoi_circuit_00() {
        let input_data = [
            vec![Felt::zero(), Felt::zero()],
            vec![Felt::one(), Felt::one()],
            vec![Felt::zero(), Felt::one()],
            vec![Felt::one(), Felt::zero()],
            vec![Felt::from_raw([
                0x1c25e48625ed6689,
                0x2c4b560cc6d4310b,
                0xb9180634b3117226,
                0x6f41ed4dc66617c,
            ]),
            Felt::from_raw([
                0xc2623c038b4e4821,
                0xa296c787ff3bfaf7,
                0x4376df758f37558f,
                0xf5cb7e5e6e8e60b,
            ]),]
        ]; 

        let expected = [
            Felt::from_raw([
                0x94672c47f345700a,
                0xe5168077fd5eeb90,
                0xae14f132fcc041ec,
                0x2ac427786f4818bf,]
            ),
            Felt::from_raw([
                0x9f72277137a37266,
                0x17bdddc79f44f08b,
                0x76008edf3b0d7d10,
                0x11f013adb9e0ff65,]
            ),
            Felt::from_raw([
                0x9d1c52ced652aaa4,
                0x7906980e70afe1f3,
                0xe62de82fa248f127,
                0x1a5486526f2983a4]
            ),
            Felt::from_raw([
                0xf8f9b631df3b5946,
                0x457b76a4dd3a7232,
                0xc961800cfaeb18c,
                0x2ef87685dfc3d604]
            ),
            Felt::from_raw([
                0xe36fdee96b617406,
                0x18371710b0763c58,
                0xed30f47d4936b9d0,
                0x2a61789d490e1fd4,
            ])
        ];

        for i in 0..4 {
            let test_circuit = TestCircuit {inputs: input_data[i].clone(), result: expected[i]};
            let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), Ok(()));
        }

    }

}

