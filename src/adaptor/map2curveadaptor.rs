use crate::adaptor::field_to_bn;
use crate::adaptor::get_selected_entries;
use crate::circuits::map_to_curve::{Map2CurveChip, Map2CurveChipConfig};
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst::{ Map2CurvePush, Map2CurveResult};
use crate::utils::Limb;
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bls12_381::{Fq, G1Affine};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::{Advice, Column, Error};
use halo2ecc_s::context::{Context,GeneralScalarEccContext};
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::assign::{AssignedFq2};
use halo2ecc_s::circuit::base_chip::BaseChip;
use halo2ecc_s::circuit::range_chip::RangeChip;
use halo2ecc_s::circuit::select_chip::SelectChip;
use std::cell::RefCell;
use std::rc::Rc;


const MERGE_SIZE: usize = 4;
//re+image+result(rex,imx,rey,imy)
const CHUNK_SIZE: usize = (2 + 2 + 2) * MERGE_SIZE;

const TOTAL_CONSTRUCTIONS: usize = 400;


fn map_2_curve_default_table<F: FieldExt>(inputs: &Vec<F>) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    r.push(crate::adaptor::fr_to_args(inputs[0],4, 64, Map2CurvePush));
    r.push(crate::adaptor::fr_to_args(inputs[1],4, 64, Map2CurvePush));
    r.push(crate::adaptor::fr_to_args(inputs[2],4, 64, Map2CurveResult));
    r.push(crate::adaptor::fr_to_args(inputs[3],4, 64, Map2CurveResult));
    r.push(crate::adaptor::fr_to_args(inputs[4],4, 64, Map2CurveResult));
    r.push(crate::adaptor::fr_to_args(inputs[5],4, 64, Map2CurveResult));
    r.into_iter().flatten().collect::<Vec<_>>()
}

impl HostOpSelector for Map2CurveChip<Fr> {
    type Config = Map2CurveChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Map2CurveChip::configure(meta, shared_advice)
    }

    fn construct(c: Self::Config) -> Self {
        Map2CurveChip::new(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(Map2CurvePush as u64),
            Fr::from(Map2CurveResult as u64),
        ]
    }

    fn assign(
        region: &mut Region<Fr>,
        k: usize,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        println!("host op assign {}!", offset);
        let opcodes = Self::opcodes();
        let selected_entries = get_selected_entries(shared_operands, shared_opcodes, &opcodes);
        let total_used_instructions = selected_entries.len() / (CHUNK_SIZE);

        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            // let ((operand, opcode), index) = *group.get(0).clone().unwrap();
            // assert!(opcode.clone() == Fr::from(Map2CurvePush as u64));

            for subgroup in group
                .clone()
                .into_iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                let (limb, _) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    true,
                )?;
                r.push(limb);
            }
        }

        //todo set correct defaults
        let default_table = map_2_curve_default_table(
            &vec![Fr::one(),Fr::one(),Fr::one(),Fr::one(),Fr::one(),Fr::one()]);

        //let entries = default_table.
        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(k >= 22);
        let total_available = Self::max_rounds(k);
        assert!(total_used_instructions <= total_available);

        for _ in 0..=total_available - total_used_instructions {
            for subgroup in default_entries
                .clone()
                .iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                let (limb, _) = config.assign_merged_operands(
                    region,
                    offset,
                    subgroup.to_vec(),
                    Fr::from_u128(1u128 << 64),
                    false,
                )?;
                r.push(limb);
            }
        }

        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        println!("map2curve adaptor total args is {}", arg_cells.len());
        let timer = start_timer!(|| "assign");
        let config = self.config.clone();

        let base_chip = BaseChip::new(config.base_chip_config);
        let select_chip = SelectChip::new(config.select_chip_config);
        let range_chip = RangeChip::<Fr>::new(config.range_chip_config);

        let mut gseccc =
            GeneralScalarEccContext::<G1Affine, Fr>::new(Rc::new(RefCell::new(Context::new())));
        let mut inputs = vec![];
        let mut outputs = vec![];
        // arg_cells format  2 + 2 + 2
        let arg_groups = arg_cells.chunks_exact(6).collect::<Vec<_>>();
        for arg_group in arg_groups.iter() {
            // let args = arg_group.into_iter().map(|x| x.clone());
            // let args = args.collect::<Vec<_>>();
            let u: AssignedFq2<Fq, Fr> = (
                gseccc.base_integer_ctx.assign_w(&field_to_bn(&arg_group[0].value)),
                gseccc.base_integer_ctx.assign_w(&field_to_bn(&arg_group[1].value)),
            );
            inputs.push(u.clone());

            let (x,y) = self.simplified_swu_in_context(&mut gseccc,&u);
            outputs.push((x,y));
        }

        let context:Context<Fr> = gseccc.into();
        layouter.assign_region(
            || "base",
            |mut region| {
                let cells = context.records.lock().unwrap().assign_all_opt(
                    &mut region,
                    &base_chip,
                    &range_chip,
                    &select_chip,
                )?;

                match cells {
                    Some(cells) => {
                        for (i,input) in inputs.iter().enumerate(){
                            //input.re
                            let v = &input.0;
                            region.constrain_equal(
                                arg_groups[i][0].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;
                            //input.img
                            let v = &input.1;
                            region.constrain_equal(
                                arg_groups[i][1].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;
                            //output.x.re
                            let v = &outputs[i].0.0;
                            region.constrain_equal(
                                arg_groups[i][2].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region  as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;
                            //output.x.img
                            let v = &outputs[i].0.1;
                            region.constrain_equal(
                                arg_groups[i][3].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;
                            //output.y.re
                            let v = &outputs[i].1.0;
                            region.constrain_equal(
                                arg_groups[i][4].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;
                            //output.y.img
                            let v = &outputs[i].1.1;
                            region.constrain_equal(
                                arg_groups[i][5].cell.as_ref().unwrap().cell(),
                                cells[v.native.cell.region as usize][v.native.cell.col][v.native.cell.row].as_ref().unwrap().cell().clone()
                            )?;

                        }
                    }
                    None => {}
                }

                Ok(())
            },
        )?;
        end_timer!(timer);

        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _region: &mut Region<Fr>,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::msm_to_host_call_table;
    use crate::host::jubjub::Point;
    use crate::host::ExternalHostCallEntryTable;
    use halo2_proofs::pairing::bn256::Fr;
    use std::fs::File;

    // #[test]
    // fn generate_jubjub_msm_input() {
    //     let default_table = msm_to_host_call_table(&vec![(Point::identity(), Fr::one())]);
    //     let file = File::create("jubjub.json").expect("can not create file");
    //     serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
    //         .expect("can not write to file");
    // }
    //
    // #[test]
    // fn generate_jubjub_msm_input_multi() {
    //     let default_table = msm_to_host_call_table(&vec![(Point::identity(), Fr::one())]);
    //     let file = File::create("jubjub_multi.json").expect("can not create file");
    //     serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
    //         .expect("can not write to file");
    // }
}
