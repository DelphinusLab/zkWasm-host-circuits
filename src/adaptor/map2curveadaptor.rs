use crate::adaptor::get_selected_entries;
use crate::circuits::host::{HostOpConfig, HostOpSelector};
use crate::circuits::map_to_curve::{Map2CurveChip, Map2CurveChipConfig};
use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst::{Map2CurvePush, Map2CurveResult};
use crate::utils::Limb;
use ark_std::{end_timer, start_timer};
use halo2_proofs::arithmetic::{BaseExt, FieldExt};
use halo2_proofs::circuit::{Layouter, Region};
use halo2_proofs::pairing::bls12_381::Fq;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::{Advice, Column, Error};
use halo2ecc_s::utils::bn_to_field;
use num_bigint::BigUint;
use std::str::FromStr;

//bls381 need 8*u54
const MERGE_SIZE: usize = 8;

//input(re,im)+result_x(re,im)+result_y(re,im)
const CHUNK_SIZE: usize = (2 + 2 + 2) * MERGE_SIZE;

//1 limb = 2*u54
pub const MAP2CURVE_LIMBS_SIZE: usize = CHUNK_SIZE / 2;

const TOTAL_CONSTRUCTIONS: usize = 1;

fn map_2_curve_default_table<F: BaseExt>(inputs: &Vec<F>) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    r.push(crate::adaptor::fr_to_args(
        inputs[0],
        MERGE_SIZE,
        54,
        Map2CurvePush,
    ));
    r.push(crate::adaptor::fr_to_args(
        inputs[1],
        MERGE_SIZE,
        54,
        Map2CurvePush,
    ));
    r.push(crate::adaptor::fr_to_args(
        inputs[2],
        MERGE_SIZE,
        54,
        Map2CurveResult,
    ));
    r.push(crate::adaptor::fr_to_args(
        inputs[3],
        MERGE_SIZE,
        54,
        Map2CurveResult,
    ));
    r.push(crate::adaptor::fr_to_args(
        inputs[4],
        MERGE_SIZE,
        54,
        Map2CurveResult,
    ));
    r.push(crate::adaptor::fr_to_args(
        inputs[5],
        MERGE_SIZE,
        54,
        Map2CurveResult,
    ));
    r.into_iter().flatten().collect::<Vec<_>>()
}

impl HostOpSelector for Map2CurveChip<Fr> {
    type Config = Map2CurveChipConfig;
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advice: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Map2CurveChip::configure(meta)
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
        println!("total used instructions: {}", total_used_instructions);

        let mut r = vec![];

        for group in selected_entries.chunks_exact(CHUNK_SIZE) {
            for subgroup in group
                .clone()
                .into_iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                for i in 0..MERGE_SIZE / 2 {
                    let (limb, _) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![subgroup[2 * i], subgroup[2 * i + 1]],
                        Fr::from_u128(1u128 << 54),
                        true,
                    )?;
                    r.push(limb);
                }
            }
        }

        let u_re_bn = BigUint::from_str("593868448310005448561172252387029516360409945786457439875974315031640021389835649561235021338510064922970633805048").unwrap();
        let u_im_bn = BigUint::from_str("867375309489067512797459860887365951877054038763818448057326190302701649888849997836339069389536967202878289851290").unwrap();

        let x_re_bn = BigUint::from_str("3942339120143403995959884458065911863622623490130179671696530864527894030375709350085997343451924840375271949093332").unwrap();
        let x_im_bn = BigUint::from_str("3523381697296058645143708860912139218718520142948191822158638626523448297128525915027995335789050238781038107799201").unwrap();
        let y_re_bn = BigUint::from_str("1842813153358560687634500333570189006426514559071004676715031705637331861897467026112259097700599015948196491964104").unwrap();
        let y_im_bn = BigUint::from_str("1919560373509329990190398196596248904228486898136222165059580822353869402983639316101175960854421770934878934628156").unwrap();

        let default_table = map_2_curve_default_table(&vec![
            bn_to_field::<Fq>(&u_re_bn),
            bn_to_field::<Fq>(&u_im_bn),
            bn_to_field::<Fq>(&x_re_bn),
            bn_to_field::<Fq>(&x_im_bn),
            bn_to_field::<Fq>(&y_re_bn),
            bn_to_field::<Fq>(&y_im_bn),
        ]);

        let default_entries: Vec<((Fr, Fr), Fr)> = default_table
            .into_iter()
            .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
            .collect::<Vec<((Fr, Fr), Fr)>>();

        assert!(k >= 22);
        let total_available = Self::max_rounds(k);
        assert!(total_used_instructions <= total_available);

        for _ in 0..total_available - total_used_instructions {
            for subgroup in default_entries
                .clone()
                .iter()
                .collect::<Vec<_>>()
                .chunks_exact(MERGE_SIZE)
            {
                for i in 0..MERGE_SIZE / 2 {
                    let (limb, _) = config.assign_merged_operands(
                        region,
                        offset,
                        vec![subgroup[2 * i], subgroup[2 * i + 1]],
                        Fr::from_u128(1u128 << 54),
                        false,
                    )?;
                    r.push(limb);
                }
            }
        }

        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        layouter: &mut impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let timer = start_timer!(|| "synthesize map2curve");
        self.range_chip.init_table(layouter)?;
        self.load_map2curve_circuit(arg_cells, layouter)?;
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
    use crate::adaptor::map2curveadaptor::map_2_curve_default_table;
    use crate::host::ExternalHostCallEntryTable;
    use halo2_proofs::pairing::bls12_381::Fq;
    use halo2ecc_s::utils::bn_to_field;
    use num_bigint::BigUint;
    use std::fs::File;
    use std::str::FromStr;

    #[test]
    fn generate_map2curve_input() {
        let u_re_bn = BigUint::from_str("593868448310005448561172252387029516360409945786457439875974315031640021389835649561235021338510064922970633805048").unwrap();
        let u_im_bn = BigUint::from_str("867375309489067512797459860887365951877054038763818448057326190302701649888849997836339069389536967202878289851290").unwrap();

        let x_re_bn = BigUint::from_str("3942339120143403995959884458065911863622623490130179671696530864527894030375709350085997343451924840375271949093332").unwrap();
        let x_im_bn = BigUint::from_str("3523381697296058645143708860912139218718520142948191822158638626523448297128525915027995335789050238781038107799201").unwrap();
        let y_re_bn = BigUint::from_str("1842813153358560687634500333570189006426514559071004676715031705637331861897467026112259097700599015948196491964104").unwrap();
        let y_im_bn = BigUint::from_str("1919560373509329990190398196596248904228486898136222165059580822353869402983639316101175960854421770934878934628156").unwrap();

        let u_re = bn_to_field::<Fq>(&u_re_bn);
        let u_im = bn_to_field::<Fq>(&u_im_bn);
        let x_re = bn_to_field::<Fq>(&x_re_bn);
        let x_im = bn_to_field::<Fq>(&x_im_bn);
        let y_re = bn_to_field::<Fq>(&y_re_bn);
        let y_im = bn_to_field::<Fq>(&y_im_bn);

        let default_table = map_2_curve_default_table(&vec![u_re, u_im, x_re, x_im, y_re, y_im]);
        let file = File::create("map2curve.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &ExternalHostCallEntryTable(default_table))
            .expect("can not write to file");
    }
}
