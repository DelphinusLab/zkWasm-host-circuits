use crate::circuits::{LookupAssistChip, LookupAssistConfig};
use crate::utils::{bn_to_field, field_to_bn, GateCell, Limb};
use crate::{
    constant_from, customized_circuits, customized_circuits_expand, item_count, table_item,
    value_for_assign,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use num_bigint::BigUint;
use std::marker::PhantomData;
use std::ops::Div;

#[rustfmt::skip]
customized_circuits!(KeccakArithConfig, 2, 7, 2, 0,
   | lhs   |  rhs   |  res   |  rem   |  acc_lhs   |  acc_rhs  |  acc_res  | table  |  sel
   | nil   |  nil   |  nil   |  rem_n |  acc_n_lhs | acc_n_rhs | acc_n_res |  nil   |  sel_n
);

impl LookupAssistConfig for KeccakArithConfig {
    /// register columns (col) to be XOR checked by limb size (sz)
    fn register<F: FieldExt>(
        &self,
        cs: &mut ConstraintSystem<F>,
        col: impl FnOnce(&mut VirtualCells<F>) -> Expression<F> + Copy,
        sz: impl FnOnce(&mut VirtualCells<F>) -> Expression<F> + Copy,
    ) {
        cs.lookup_any("check lhs", |meta| {
            let acc_lhs = self.get_expr(meta, KeccakArithConfig::acc_lhs());
            let rem = self.get_expr(meta, KeccakArithConfig::rem());
            vec![(col(meta), acc_lhs), (sz(meta), rem)]
        });

        cs.lookup_any("check rhs", |meta| {
            let acc_rhs = self.get_expr(meta, KeccakArithConfig::acc_rhs());
            let rem = self.get_expr(meta, KeccakArithConfig::rem());
            vec![(col(meta), acc_rhs), (sz(meta), rem)]
        });
    }
}

pub struct KeccakArithChip<F: FieldExt> {
    config: KeccakArithConfig,
    offset: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LookupAssistChip<F> for KeccakArithChip<F> {
    fn provide_lookup_evidence(
        &mut self,
        _region: &mut Region<F>,
        _value: F,
        _sz: u64,
    ) -> Result<(), Error> {
        Ok(())
    }

    /*
    fn provide_xor_lookup_evidence (
        &mut self,
        region: &mut Region<F>,
        lhs: F,
        rhs: F,
        sz: u64,
    ) -> Result<(), Error> {
        self.assign_value_xor(region, lhs, rhs, sz);
        //self.assign_value_and(region, value, sz);
        Ok(())
    }

     */
}

impl<F: FieldExt> KeccakArithChip<F> {
    pub fn new(config: KeccakArithConfig) -> Self {
        KeccakArithChip {
            config,
            offset: 0,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> KeccakArithConfig {
        let witness = [0; 7].map(|_| cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 2].map(|_| cs.fixed_column());
        let selector = [];

        let config = KeccakArithConfig {
            fixed,
            selector,
            witness,
        };

        // Check if the encoding of (lhs, rhs, res) belongs to the table
        cs.lookup_any("xor validity check", |meta| {
            let res = config.get_expr(meta, KeccakArithConfig::res());
            let lhs = config.get_expr(meta, KeccakArithConfig::lhs());
            let rhs = config.get_expr(meta, KeccakArithConfig::rhs());
            let table = config.get_expr(meta, KeccakArithConfig::table());
            let pow16 = constant_from!(1u64 << 16);
            let pow8 = constant_from!(1u64 << 8);

            vec![(lhs * pow16 + rhs * pow8 + res, table)]
        });

        // First we require the rem is continues if it is not zero
        cs.create_gate("arith check constraint", |meta| {
            let rem = config.get_expr(meta, KeccakArithConfig::rem());
            let rem_n = config.get_expr(meta, KeccakArithConfig::rem_n());
            let sel = config.get_expr(meta, KeccakArithConfig::sel());

            vec![sel * rem.clone() * (rem - rem_n - constant_from!(1))]
        });

        // Second we make sure if the rem is not zero then
        // carry = carry_n * 2^8 + limb
        cs.create_gate("limb acc constraint", |meta| {
            let lhs = config.get_expr(meta, KeccakArithConfig::lhs());
            let acc_lhs = config.get_expr(meta, KeccakArithConfig::acc_lhs());
            let acc_n_lhs = config.get_expr(meta, KeccakArithConfig::acc_n_lhs());

            let rhs = config.get_expr(meta, KeccakArithConfig::rhs());
            let acc_rhs = config.get_expr(meta, KeccakArithConfig::acc_rhs());
            let acc_n_rhs = config.get_expr(meta, KeccakArithConfig::acc_n_rhs());

            let res = config.get_expr(meta, KeccakArithConfig::res());
            let acc_res = config.get_expr(meta, KeccakArithConfig::acc_res());
            let acc_n_res = config.get_expr(meta, KeccakArithConfig::acc_n_res());

            let sel = config.get_expr(meta, KeccakArithConfig::sel());
            let sel_n = config.get_expr(meta, KeccakArithConfig::sel_n());

            vec![
                sel.clone()
                    * (acc_lhs.clone()
                        - lhs
                        - acc_n_lhs * constant_from!(1u64 << 8) * sel_n.clone()),
                sel.clone()
                    * (acc_rhs.clone()
                        - rhs
                        - acc_n_rhs * constant_from!(1u64 << 8) * sel_n.clone()),
                sel.clone()
                    * (acc_res.clone()
                        - res
                        - acc_n_res * constant_from!(1u64 << 8) * sel_n.clone()),
                sel.clone() * (constant_from!(1) - sel.clone()),
                //(constant_from!(1) - sel) * acc, // if sel is 0 then acc must equal to 0
            ]
        });

        cs.create_gate("end with zero", |meta| {
            let sel = config.get_expr(meta, KeccakArithConfig::sel());
            let acc_n_lhs = config.get_expr(meta, KeccakArithConfig::acc_n_lhs());
            let acc_n_rhs = config.get_expr(meta, KeccakArithConfig::acc_n_rhs());
            let acc_n_res = config.get_expr(meta, KeccakArithConfig::acc_n_res());
            let sel_n = config.get_expr(meta, KeccakArithConfig::sel_n());

            vec![
                sel.clone() * acc_n_lhs * (constant_from!(1) - sel_n.clone()), // if sel is 0 then acc must equal to 0
                sel.clone() * acc_n_rhs * (constant_from!(1) - sel_n.clone()),
                sel * acc_n_res * (constant_from!(1) - sel_n),
            ]
        });

        config
    }

    pub fn assign_value_xor(
        &mut self,
        region: &mut Region<F>,
        lhs: F,
        rhs: F,
        sz: u64,
    ) -> Result<(), Error> {
        let mut limbs_lhs = vec![];
        let mut limbs_rhs = vec![];
        let mut limbs_res = vec![];

        let mut bn_lhs = field_to_bn(&lhs);
        let mut bn_rhs = field_to_bn(&rhs);
        let mut bn_res = bn_lhs.clone() ^ bn_rhs.clone();

        let mut cs_lhs = vec![];
        let mut cs_rhs = vec![];
        let mut cs_res = vec![];

        for _ in 0..sz {
            cs_lhs.push(bn_to_field(&bn_lhs));
            cs_rhs.push(bn_to_field(&bn_rhs));
            cs_res.push(bn_to_field(&bn_res));

            let limb_lhs = bn_lhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 8));
            let limb_rhs = bn_rhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 8));
            let limb_res = bn_res.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 8));

            bn_lhs = (bn_lhs - limb_lhs.clone()).div(BigUint::from(1u128 << 8));
            bn_rhs = (bn_rhs - limb_rhs.clone()).div(BigUint::from(1u128 << 8));
            bn_res = (bn_res - limb_res.clone()).div(BigUint::from(1u128 << 8));

            limbs_lhs.push(bn_to_field(&limb_lhs));
            limbs_rhs.push(bn_to_field(&limb_rhs));
            limbs_res.push(bn_to_field(&limb_res));
        }
        cs_lhs.reverse();
        cs_rhs.reverse();
        cs_res.reverse();

        limbs_lhs.reverse();
        limbs_rhs.reverse();
        limbs_res.reverse();

        for i in 0..sz {
            let limb_lhs = limbs_lhs.pop().unwrap();
            let limb_rhs = limbs_rhs.pop().unwrap();
            let limb_res = limbs_res.pop().unwrap();
            let acc_lhs = cs_lhs.pop().unwrap();
            let acc_rhs = cs_rhs.pop().unwrap();
            let acc_res = cs_res.pop().unwrap();

            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::lhs(), limb_lhs)?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::acc_lhs(), acc_lhs)?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::res(), limb_res)?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::acc_res(), acc_res)?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::rhs(), limb_rhs)?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::acc_rhs(), acc_rhs)?;
            self.config.assign_cell(
                region,
                self.offset,
                &KeccakArithConfig::rem(),
                F::from_u128((sz - i) as u128),
            )?;
            self.config
                .assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::one())?;

            self.offset += 1;
        }
        self.config
            .assign_cell(region, self.offset, &KeccakArithConfig::lhs(), F::zero())?;
        self.config
            .assign_cell(region, self.offset, &KeccakArithConfig::rhs(), F::zero())?;
        self.config
            .assign_cell(region, self.offset, &KeccakArithConfig::res(), F::zero())?;
        self.config.assign_cell(
            region,
            self.offset,
            &KeccakArithConfig::acc_lhs(),
            F::zero(),
        )?;
        self.config.assign_cell(
            region,
            self.offset,
            &KeccakArithConfig::acc_rhs(),
            F::zero(),
        )?;
        self.config.assign_cell(
            region,
            self.offset,
            &KeccakArithConfig::acc_res(),
            F::zero(),
        )?;
        self.config
            .assign_cell(region, self.offset, &KeccakArithConfig::rem(), F::zero())?;
        self.config
            .assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::zero())?;
        self.offset += 1;
        Ok(())
    }

    /// initialize the table columns that contains every possible result of 4-bit value via XOR or ADD operation
    /// initialize needs to be called before using the KeccarkArithchip
    pub fn initialize(&mut self, region: &mut Region<F>) -> Result<(), Error> {
        // initialize the XOR table with the encoded value
        for i in 0..1 << 8 {
            for j in 0..1 << 8 {
                let res = i ^ j;
                self.config.assign_cell(
                    region,
                    i * (1 << 8) + j,
                    &KeccakArithConfig::table(),
                    F::from_u128((i * (1 << 16) + j * (1 << 8) + res) as u128),
                )?;
            }
        }
        self.offset = 0;
        self.assign_value_xor(region, F::zero(), F::zero(), 8)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr;

    use halo2_proofs::{
        circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, VirtualCells},
        poly::Rotation,
    };

    use super::{KeccakArithChip, KeccakArithConfig};
    use crate::circuits::LookupAssistConfig;
    use crate::utils::{bn_to_field, field_to_bn};
    use crate::value_for_assign;

    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb_lhs: Column<Advice>,
        limb_rhs: Column<Advice>,
    }

    impl HelperChipConfig {
        pub fn arith_check_lhs(&self, cs: &mut VirtualCells<Fr>) -> Expression<Fr> {
            cs.query_advice(self.limb_lhs, Rotation::cur())
        }
        pub fn arith_check_rhs(&self, cs: &mut VirtualCells<Fr>) -> Expression<Fr> {
            cs.query_advice(self.limb_rhs, Rotation::cur())
        }
        // do we need to check the result here?
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
            let limb_lhs = cs.advice_column();
            let limb_rhs = cs.advice_column();
            cs.enable_equality(limb_rhs);
            cs.enable_equality(limb_lhs);
            HelperChipConfig { limb_lhs, limb_rhs }
        }

        fn assign_lhs(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            value: Fr,
        ) -> Result<AssignedCell<Fr, Fr>, Error> {
            let v = region.assign_advice(
                || format!("assign input"),
                self.config.limb_lhs,
                *offset,
                || value_for_assign!(value),
            )?;

            *offset = *offset + 1;
            Ok(v)
        }

        fn assign_rhs(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            value: Fr,
        ) -> Result<AssignedCell<Fr, Fr>, Error> {
            let v = region.assign_advice(
                || format!("assign input"),
                self.config.limb_rhs,
                *offset,
                || value_for_assign!(value),
            )?;

            *offset = *offset + 1;
            Ok(v)
        }
    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {}

    #[derive(Clone, Debug)]
    struct TestConfig {
        keccakchipconfig: KeccakArithConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let keccakchipconfig = KeccakArithChip::<Fr>::configure(meta);
            let helperconfig = HelperChip::configure(meta);

            keccakchipconfig.register(
                meta,
                |c| helperconfig.arith_check_lhs(c),
                |_| Expression::Constant(Fr::from(8u64)),
            );

            /*
            keccakchipconfig.register(
                meta,
                |c| helperconfig.arith_check_rhs(c),
                |_| Expression::Constant(Fr::from(4u64)));
             */

            Self::Config {
                keccakchipconfig,
                helperconfig,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let mut keccak_arith_chip = KeccakArithChip::<Fr>::new(config.clone().keccakchipconfig);
            let helper_chip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "xor check test",
                |mut region| {
                    let lhs = Fr::from(1u64 << 24 + 1);
                    let bn_lhs = field_to_bn(&lhs);
                    let rhs = Fr::from(1u64 << 24 + 1);
                    let bn_rhs = field_to_bn(&rhs);
                    let bn_res = bn_lhs ^ bn_rhs;
                    let res: Fr = bn_to_field(&bn_res);
                    //let v = lhs.clone() * Fr::from(1u64<<8) + rhs.clone() * Fr::from(1u64 << 4) + res.clone();

                    keccak_arith_chip.initialize(&mut region)?;

                    keccak_arith_chip.assign_value_xor(&mut region, lhs, rhs, 8)?;

                    // assign helper
                    let mut offset = 0;

                    helper_chip.assign_lhs(&mut region, &mut offset, lhs)?;
                    helper_chip.assign_rhs(&mut region, &mut offset, rhs)?;

                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_xor_circuit() {
        let test_circuit = TestCircuit {};
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();

        let verify_result = prover.verify();
        if !verify_result.is_ok() {
            if let Some(errors) = verify_result.err() {
                for (i, error) in errors.iter().enumerate() {
                    println!(" err {}, {:?}", i, error);
                }
            }
            panic!();
        }
    }
}
