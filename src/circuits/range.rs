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
};
use std::ops::Div;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, AssignedCell},
    plonk::{
        Fixed, Advice, Column, ConstraintSystem,
        Error, Expression, Selector, VirtualCells
    },
    poly::Rotation,
};
use std::marker::PhantomData;
use num_bigint::BigUint;

/*
 * Customized gates range_check(target)
 * limbs \in table
 * sum limbs * acc will be the sum of the target
 */
customized_circuits!(RangeCheckConfig, 2, 3, 2, 0,
   | limb   |  acc   | rem   | table | sel
   | nil    |  acc_n | rem_n | nil   | sel_n
);

pub struct RangeCheckChip<F:FieldExt> {
    config: RangeCheckConfig,
    offset: usize,
    _marker: PhantomData<F>
}


impl<F: FieldExt> RangeCheckChip<F> {
    pub fn new(config: RangeCheckConfig) -> Self {
        RangeCheckChip {
            config,
            offset: 0,
            _marker: PhantomData,
        }
    }

    pub fn register_range(
        &self,
        meta: &mut ConstraintSystem<F>,
        column: impl FnOnce(&mut VirtualCells<F>)->Expression<F>,
        index: impl FnOnce(&mut VirtualCells<F>)->Expression<F>) {
        meta.lookup_any("register range", |meta| {
            let acc = self.config.get_expr(meta, RangeCheckConfig::acc());
            let rem = self.config.get_expr(meta, RangeCheckConfig::rem());
            let column = column(meta);
            let index = index(meta);
            vec![(acc, column), (rem, index)]
        });
        ()
    }

    pub fn configure(cs: &mut ConstraintSystem<F>) -> RangeCheckConfig {
        let witness= [0; 3]
                .map(|_|cs.advice_column());
        witness.map(|x| cs.enable_equality(x));
        let fixed = [0; 2].map(|_| cs.fixed_column());
        let selector =[];

        let config = RangeCheckConfig { fixed, selector, witness };

        // Range Check of all limbs
        cs.lookup_any("within ranges", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let table = config.get_expr(meta, RangeCheckConfig::table());
            vec![(limb, table)]
        });



        // First we require the rem is continus if it is not zero
        cs.create_gate("range check constraint", |meta| {
            let rem = config.get_expr(meta, RangeCheckConfig::rem());
            let rem_n = config.get_expr(meta, RangeCheckConfig::rem_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());

            vec![
                sel * rem.clone() * (rem - rem_n - constant_from!(1))
            ]

        });

        // Second we make sure if the rem is not zero then
        // carry = carry_n * 2^12 + limb
        // for example, suppose we have range check with 5 limb
        // | a_0 | carry_0 | 5 | 1 |
        // | a_1 | carry_1 | 4 | 1 |
        // | a_2 | carry_2 | 3 | 1 |
        // | a_3 | carry_3 | 2 | 1 |
        // | a_4 | carry_4 | 1 | 1 |
        // | nil | 0       | 0 | 0 |
        cs.create_gate("limb acc constraint", |meta| {
            let limb = config.get_expr(meta, RangeCheckConfig::limb());
            let acc = config.get_expr(meta, RangeCheckConfig::acc());
            let acc_n = config.get_expr(meta, RangeCheckConfig::acc_n());
            let sel = config.get_expr(meta, RangeCheckConfig::sel());
            let sel_n = config.get_expr(meta, RangeCheckConfig::sel_n());

            vec![
                sel * (acc - limb - acc_n * constant_from!(2u64<<12) * sel_n)
            ]

        });
        config
    }

    pub fn assign_value_with_range (
        &mut self,
        region: &mut Region<F>,
        value: F,
        sz: usize,
    ) -> Result<(), Error> {
        let mut limbs = vec![];
        let mut bn = field_to_bn(&value);
        let mut cs = vec![];
        for _ in 0..sz {
            cs.push(bn_to_field(&bn));
            let limb = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128<<108));
            bn = (bn - limb.clone()).div(BigUint::from(1u128<<108));
            limbs.push(bn_to_field(&limb));
        }
        for i in 0..sz {
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::limb(), limbs.pop().unwrap())?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::acc(), cs.pop().unwrap())?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::rem(), F::from_u128((sz-i) as u128))?;
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::sel(), F::one())?;
            self.offset += 1;
        }
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::limb(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::acc(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::rem(), F::zero())?;
        self.config.assign_cell(region, self.offset, &RangeCheckConfig::sel(), F::zero())?;
        Ok(())
    }

    pub fn initialize(
        &self,
        region: &mut Region<F>
    ) -> Result<(), Error> {
        for i in 0..4096 {
            self.config.assign_cell(region, self.offset, &RangeCheckConfig::table(), F::from_u128(i as u128))?;
        }
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::dev::MockProver;
    use num_bigint::BigUint;

    use halo2_proofs::{
        circuit::{Chip, Layouter, Region, SimpleFloorPlanner},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error
        },
    };

    use super::{
        ModExpChip,
        ModExpConfig,
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
                    || Ok(n.limbs[i].value)
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
        modexpconfig: ModExpConfig,
        helperconfig: HelperChipConfig,
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            Self::Config {
               modexpconfig: ModExpChip::<Fr>::configure(meta),
               helperconfig: HelperChip::configure(meta)
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let modexpchip = ModExpChip::<Fr>::new(config.clone().modexpconfig);
            let helperchip = HelperChip::new(config.clone().helperconfig);
            layouter.assign_region(
                || "assign mod mult",
                |mut region| {
                    todo!();
                    Ok(())
                }
            )?;
            Ok(())
        }
    }


    #[test]
    fn test_modexp_circuit() {
        let base = BigUint::from(1u128 << 100);
        let exp = BigUint::from(2u128 << 100);
        let modulus = BigUint::from(7u128);
        let test_circuit = TestCircuit {base, exp, modulus} ;
        let prover = MockProver::run(16, &test_circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}


