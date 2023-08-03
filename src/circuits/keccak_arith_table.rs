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
    constant_from,
    value_for_assign,
};
use crate::circuits::{
    LookupAssistConfig,
    LookupAssistChip
};
use std::ops::Div;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;


/*
 * Customized gates xor_check(target) with each limb less than 2^8
 * acc will be the sum of the target limbs and rem is the remaining limbs
 * of the target value.
customized_circuits!(KeccakArithConfig, 2, 6, 4, 0,
   | lhs   |  rhs   |  res   |  rem   |  acc_lhs   |  acc_rhs  |  table_lhs  |  table_rhs  |  table_res  |  sel
   | nil   |  nil   |  nil   |  rem_n |  acc_n_lhs | acc_n_rhs |     nil     |     nil     |     nil     |  sel_n
);
 */

customized_circuits!(RangeCheckConfig, 2, 3, 2, 0,
    | limb   |  acc   | rem   | table | sel
    | nil    |  acc_n | rem_n | nil   | sel_n
 );
impl LookupAssistConfig for KeccakArithConfig {
    /// register a columns (col) to be XOR / ADD checked by limb size (sz)
    fn register<F: FieldExt> (
        &self,
        cs: &mut ConstraintSystem<F>,
        col: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        sz: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) {
        cs.lookup_any("check lhs", |meta| {
            let acc = self.get_expr(meta, KeccakArithConfig::acc_lhs());
            let rem = self.get_expr(meta, KeccakArithConfig::rem());
            vec![(col(meta), acc), (sz(meta), rem)]
        });
    }

}

pub struct KeccakArithChip<F:FieldExt> {
    config: KeccakArithConfig,
    offset: usize,
    _marker: PhantomData<F>
}

impl<F:FieldExt> LookupAssistChip<F> for KeccakArithChip<F> {

    fn provide_lookup_evidence (
        &mut self,
        region: &mut Region<F>,
        value: F,
        sz: u64,
    ) -> Result<(), Error> {
        //self.assign_value_xor(region, value, sz);
        //self.assign_value_and(region, value, sz);
        
        Ok(())
    }
}


impl<F: FieldExt> KeccakArithChip<F> {
    pub fn new(config: KeccakArithConfig) -> Self {
        KeccakArithChip {
            config,
            offset:0,
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> KeccakArithConfig {
        let witness= [0; 6]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 4].map(|_| cs.fixed_column());
        let selector =[];

        let config = KeccakArithConfig { fixed, selector, witness };

        // Check if the relation of lhs XOR rhs equals to res belongs to the table
        //
        cs.lookup_any("within ranges", |meta| {
            let res = config.get_expr(meta, KeccakArithConfig::res());
            let table_res = config.get_expr(meta, KeccakArithConfig::table_res());

            let lhs = config.get_expr(meta, KeccakArithConfig::acc_lhs());
            let table_lhs = config.get_expr(meta, KeccakArithConfig::table_lhs());

            let rhs = config.get_expr(meta, KeccakArithConfig::acc_rhs());
            let table_rhs = config.get_expr(meta, KeccakArithConfig::table_rhs());

            vec![(res, table_res), (lhs, table_lhs), (rhs, table_rhs)]
        });

        // First we require the rem is continuos if it is not zero
        cs.create_gate("arith check constraint", |meta| {
            let rem = config.get_expr(meta, KeccakArithConfig::rem());
            let rem_n = config.get_expr(meta, KeccakArithConfig::rem_n());
            let sel = config.get_expr(meta, KeccakArithConfig::sel());

            vec![
                sel * rem.clone() * (rem - rem_n - constant_from!(1)),
            ]

        });

        // Second we make sure if the rem is not zero then
        // carry = carry_n * 2^8 + limb
        cs.create_gate("limb acc constraint", |meta| {
            let limb = config.get_expr(meta, KeccakArithConfig::lhs());
            let acc_lhs = config.get_expr(meta, KeccakArithConfig::acc_lhs());
            let acc_n_lhs = config.get_expr(meta, KeccakArithConfig::acc_n_lhs());

            let sel = config.get_expr(meta, KeccakArithConfig::sel());
            let sel_n = config.get_expr(meta, KeccakArithConfig::sel_n());

            let limb = config.get_expr(meta, KeccakArithConfig::rhs());
            let acc_rhs = config.get_expr(meta, KeccakArithConfig::acc_rhs());
            let acc_n_rhs = config.get_expr(meta, KeccakArithConfig::acc_n_rhs());
            

            vec![
                sel.clone() * (acc_lhs.clone() - limb - acc_n_lhs * constant_from!(1u64<<8) * sel_n),
                sel.clone() * (constant_from!(1) - sel.clone()),
                sel.clone() * (acc_rhs.clone() - limb - acc_n_rhs * constant_from!(1u64<<8) * sel_n),
                //(constant_from!(1) - sel) * acc, // if sel is 0 then acc must equal to 0
            ]

        });
        cs.create_gate("end with zero", |meta| {
            let sel = config.get_expr(meta, KeccakArithConfig::sel());
            let acc_n_lhs = config.get_expr(meta, KeccakArithConfig::acc_n_lhs());
            let acc_n_rhs = config.get_expr(meta, KeccakArithConfig::acc_n_rhs());
            let sel_n = config.get_expr(meta, KeccakArithConfig::sel_n());
            
            vec![
                sel * acc_n_lhs * (constant_from!(1) - sel_n), // if sel is 0 then acc must equal to 0
                sel * acc_n_rhs * (constant_from!(1) - sel_n),
            ]
        });

        config
    }

    /* 
    pub fn assign_value_xor (
        &mut self,
        region: &mut Region<F>,
        lhs: F,
        rhs: F,
        sz: u64,
    ) -> Result<(), Error> {
        let mut limbs_lhs = vec![];
        let mut limbs_rhs = vec![];
        let mut bn_lhs = field_to_bn(&lhs);
        let mut bn_rhs = field_to_bn(&rhs);
        let mut cs_lhs = vec![];
        let mut cs_rhs = vec![];
        let mut res_vec = vec![];
        
        for _ in 0..sz {
            cs_lhs.push(bn_to_field(&bn_lhs));
            cs_rhs.push(bn_to_field(&bn_rhs));
            let limb_lhs = bn_lhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<8));
            let limb_rhs = bn_rhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<8));
            bn_lhs = (bn_lhs - limb_lhs.clone()).div(BigUint::from(1u128<<8));
            bn_rhs = (bn_rhs - limb_rhs.clone()).div(BigUint::from(1u128<<8));
            let res = limb_lhs ^ limb_rhs;
            res_vec.push(bn_to_field(&res));
            limbs_lhs.push(bn_to_field(&limb_lhs));
            limbs_rhs.push(bn_to_field(&limb_rhs));
        }
      
        cs_lhs.reverse();
        cs_rhs.reverse();
        limbs_lhs.reverse();
        limbs_rhs.reverse();
        res_vec.reverse();

        for i in 0..sz {
            let limb_lhs = limbs_lhs.pop().unwrap();
            let limb_rhs = limbs_rhs.pop().unwrap();
            let acc_lhs = cs_lhs.pop().unwrap();
            let acc_rhs = cs_rhs.pop().unwrap();
            let res = res_vec.pop().unwrap();

            self.config.assign_cell(region, self.offset, &KeccakArithConfig::lhs(), limb_lhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_lhs(), acc_lhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::rem(), F::from_u128((sz-i) as u128))?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::one())?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::res(), res)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::rhs(), limb_rhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_rhs(), acc_rhs)?;

            self.offset += 1;
        }
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::lhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::rhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_lhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_rhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::rem(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::zero())?;
        self.offset += 1;
        Ok(())
    }

    pub fn assign_value_and (
        &mut self,
        region: &mut Region<F>,
        lhs: F,
        rhs: F,
        sz: u64,
    ) -> Result<(), Error> {
        let mut limbs_lhs = vec![];
        let mut limbs_rhs = vec![];
        let mut bn_lhs = field_to_bn(&lhs);
        let mut bn_rhs = field_to_bn(&rhs);
        let mut cs_lhs = vec![];
        let mut cs_rhs = vec![];
        let mut res_vec = vec![];
        
        for _ in 0..sz {
            cs_lhs.push(bn_to_field(&bn_lhs));
            cs_rhs.push(bn_to_field(&bn_rhs));
            let limb_lhs = bn_lhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<8));
            let limb_rhs = bn_rhs.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<8));
            bn_lhs = (bn_lhs - limb_lhs.clone()).div(BigUint::from(1u128<<8));
            bn_rhs = (bn_rhs - limb_rhs.clone()).div(BigUint::from(1u128<<8));
            let res = limb_lhs + limb_rhs;
            res_vec.push(bn_to_field(&res));
            limbs_lhs.push(bn_to_field(&limb_lhs));
            limbs_rhs.push(bn_to_field(&limb_rhs));
        }
      
        cs_lhs.reverse();
        cs_rhs.reverse();
        limbs_lhs.reverse();
        limbs_rhs.reverse();
        res_vec.reverse();

        for i in 0..sz {
            let limb_lhs = limbs_lhs.pop().unwrap();
            let limb_rhs = limbs_rhs.pop().unwrap();
            let acc_lhs = cs_lhs.pop().unwrap();
            let acc_rhs = cs_rhs.pop().unwrap();
            let res = res_vec.pop().unwrap();

            self.config.assign_cell(region, self.offset, &KeccakArithConfig::lhs(), limb_lhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_lhs(), acc_lhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::rem(), F::from_u128((sz-i) as u128))?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::one())?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::res(), res)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::rhs(), limb_rhs)?;
            self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_rhs(), acc_rhs)?;

            self.offset += 1;
        }
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::lhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::rhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_lhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::acc_rhs(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::rem(), F::zero())?;
        self.config.assign_cell(region, self.offset, &KeccakArithConfig::sel(), F::zero())?;
        self.offset += 1;
        Ok(())
    }
    */

    /// initialize the table columns that contains every possible result of 8-bit value via XOR or ADD operation
    /// initialize needs to be called before using the KeccarkArithchip
    pub fn initialize(
        &mut self,
        region: &mut Region<F>,
    ) -> Result<(), Error> {
        // initialize the XOR table
        for i in 0..2^16 {
            self.config.assign_cell(region, i, &KeccakArithConfig::table_lhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::table_rhs(), F::from_u128(i as u128))?;
            // why do we need to initialize the rem and acc columns?
            self.config.assign_cell(region, i, &KeccakArithConfig::acc_lhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::acc_rhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::rem(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::table_res(), F::from_u128(i as u128))?;
        }
        self.offset = 0;
        self.assign_value_xor(region, F::zero(), F::zero(), 8)?;

        // initialize the ADD table
        for i in 2^16..2^17 {
            self.config.assign_cell(region, i, &KeccakArithConfig::table_lhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::table_rhs(), F::from_u128(i as u128))?;

            self.config.assign_cell(region, i, &KeccakArithConfig::acc_lhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::acc_rhs(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::rem(), F::from_u128(i as u128))?;
            self.config.assign_cell(region, i, &KeccakArithConfig::table_res(), F::from_u128(i as u128))?;
        }
        self.offset = 2^16;
        self.assign_value_and(region, F::zero(), F::zero(), 8)?;
        Ok(())
    }
} 


#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner, AssignedCell},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error, VirtualCells,
            Expression
        },
        poly::Rotation,
    };

    use super::{
        KeccakArithChip,
        KeccakArithConfig,
    };
    use crate::utils::{field_to_bn, bn_to_field};
    use crate::value_for_assign;
    use crate::circuits::LookupAssistConfig;


    #[derive(Clone, Debug)]
    pub struct HelperChipConfig {
        limb: Column<Advice>
    }

    impl HelperChipConfig {
        pub fn arith_check_column (&self, cs: &mut VirtualCells<Fr>) -> Expression<Fr> {
            cs.query_advice(self.limb, Rotation::cur())
        }
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
            let limb = cs.advice_column();
            cs.enable_equality(limb);
            HelperChipConfig {
                limb,
            }
        }

        fn assign_value(
            &self,
            region: &mut Region<Fr>,
            offset: &mut usize,
            value: Fr,
        ) -> Result<AssignedCell<Fr, Fr>, Error> {
            let c = region.assign_advice(
                || format!("assign input"),
                self.config.limb,
                *offset,
                || value_for_assign!(value)
            )?;

            *offset = *offset + 1;
            Ok(c)
        }

    }

    #[derive(Clone, Debug, Default)]
    struct TestCircuit {
    }

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
                |c| helperconfig.arith_check_column(c),
                |_| Expression::Constant(Fr::from(4 as u64))
            );

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
                    let lhs = Fr::from(1u64<<24 + 1);
                    let u_lhs = field_to_bn(&lhs);
                    let rhs = Fr::from(1u64<<24 + 1);
                    let u_rhs = field_to_bn(&rhs);
                    let v = bn_to_field(&(u_lhs ^ u_rhs));
            
                    keccak_arith_chip.initialize(&mut region)?;
                    keccak_arith_chip.assign_value_xor(&mut region, lhs, rhs,  8)?;

                    // assign helper
                    let mut offset = 0;
                    helper_chip.assign_value(&mut region, &mut offset, v)?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_range_circuit() {
        let test_circuit = TestCircuit {} ;
        let prover = MockProver::run(18, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
