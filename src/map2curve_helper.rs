use delphinus_zkwasm::runtime::host::host_env::HostEnv;
use delphinus_zkwasm::runtime::host::ForeignContext;
use delphinus_zkwasm::runtime::host::ForeignStatics;
use halo2_proofs::arithmetic::CurveAffine;
use std::rc::Rc;
use zkwasm_host_circuits::circuits::map2curve::Map2CurveChip;
use zkwasm_host_circuits::circuits::host::HostOpSelector;
use zkwasm_host_circuits::host::ForeignInst;

#[derive(Default)]
struct Map2CurveContext {
    pub k: u32,
    pub result_limbs: Vec<u64>,
    pub result_cursor: usize,
    pub input_limbs: Vec<u64>,
    pub used_round: usize, // max round = 1
}

impl Map2CurveContext {
    fn bls381_g2_to_limbs(&mut self, g: G2Affine) {
        // Convert G2Affine point to limbs and store in self.result_limbs
        // Implement the conversion logic based on your specific requirements
        // For example, you can use the bls381_fq_to_limbs function from the BLS12-381 helper
        bls381_fq_to_limbs(&mut self.result_limbs, g.0.c0);
        bls381_fq_to_limbs(&mut self.result_limbs, g.0.c1);
        bls381_fq_to_limbs(&mut self.result_limbs, g.1.c0);
        bls381_fq_to_limbs(&mut self.result_limbs, g.1.c1);
    }
}

impl ForeignContext for Map2CurveContext {
    fn get_statics(&self) -> Option<ForeignStatics> {
        Some(ForeignStatics {
            used_round: self.used_round,
            max_round: Map2CurveChip::max_rounds(self.k as usize),
        })
    }
}

use specs::external_host_call_table::ExternalHostCallSignature;
pub fn register_map2curve_foreign(env: &mut HostEnv) {
    let foreign_map2curve_plugin = env
        .external_env
        .register_plugin("foreign_map2curve", Box::new(Map2CurveContext::default()));

    env.external_env.register_function(
        "map2curve_push",
        ForeignInst::Map2CurvePush as usize,
        ExternalHostCallSignature::Argument,
        foreign_map2curve_plugin.clone(),
        Rc::new(
            |_obs, context: &mut dyn ForeignContext, args: wasmi::RuntimeArgs| {
                let context = context.downcast_mut::<Map2CurveContext>().unwrap();
                for i in 0..args.len() { context.input_limbs.push(args.nth(0));}
                None
            },
        ),
    );

    env.external_env.register_function(
        "map2curve_result",
        ForeignInst::Map2CurveResult as usize,
        ExternalHostCallSignature::Argument,
        foreign_map2curve_plugin.clone(),
        Rc::new(
            |_obs, context: &mut dyn ForeignContext, _args: wasmi::RuntimeArgs| {
                assert!(context.input_limbs.len() == 16); // 1 fq2 element
                if context.result_cursor == 0 {
                    let context = context.downcast_mut::<Map2CurveContext>().unwrap();
                    let u = fetch_fq2(&context.limbs, 0); // 8 * 2 * 54
                    let output = context.map2curve(u);
                    context.bls381_g2_to_limbs(output);
                    context.used_round += 1;
                }
                let ret = Some(wasmi::RuntimeValue::I64(
                    context.result_limbs[context.result_cursor] as i64));

                context.result_cursor += 1;

                ret
            },
        ),
    );

}