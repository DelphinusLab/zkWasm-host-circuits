#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::utils::field_to_bn;
    use halo2_proofs::pairing::bn256::pairing;
    use halo2_proofs::pairing::bn256::{Fq as Bn256Fq, G1Affine, G2Affine, Gt as Bn256Gt, G1, G2};
    use halo2_proofs::pairing::group::Group;
    use num_bigint::BigUint;
    use rand::rngs::OsRng;
    use std::fs::File;
    use std::ops::Add;

    fn bn256_fr_to_args(f: Bn256Fq, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut bn = field_to_bn(&f);
        let mut ret = vec![];
        for _ in 0..5 {
            let d: BigUint = BigUint::from(1u64 << 54);
            let r = bn.clone() % d.clone();
            let value = if r == BigUint::from(0 as u32) {
                0 as u64
            } else {
                r.to_u64_digits()[0]
            };
            println!("d is {:?}, remainder is {:?}", d, r);
            bn = bn / d;
            let entry = ExternalHostCallEntry {
                op: op as usize,
                value,
                is_ret: false,
            };
            ret.append(&mut vec![entry]);
        }
        ret
    }

    fn bn256_gt_to_pair_args(f: Bn256Gt) -> Vec<ExternalHostCallEntry> {
        let c000 = bn256_fr_to_args(f.0.c0.c0.c0, ForeignInst::Bn254PairG3);
        let c001 = bn256_fr_to_args(f.0.c0.c0.c1, ForeignInst::Bn254PairG3);
        let c010 = bn256_fr_to_args(f.0.c0.c1.c0, ForeignInst::Bn254PairG3);
        let c011 = bn256_fr_to_args(f.0.c0.c1.c1, ForeignInst::Bn254PairG3);
        let c020 = bn256_fr_to_args(f.0.c0.c2.c0, ForeignInst::Bn254PairG3);
        let c021 = bn256_fr_to_args(f.0.c0.c2.c1, ForeignInst::Bn254PairG3);
        let c100 = bn256_fr_to_args(f.0.c1.c0.c0, ForeignInst::Bn254PairG3);
        let c101 = bn256_fr_to_args(f.0.c1.c0.c1, ForeignInst::Bn254PairG3);
        let c110 = bn256_fr_to_args(f.0.c1.c1.c0, ForeignInst::Bn254PairG3);
        let c111 = bn256_fr_to_args(f.0.c1.c1.c1, ForeignInst::Bn254PairG3);
        let c120 = bn256_fr_to_args(f.0.c1.c2.c0, ForeignInst::Bn254PairG3);
        let c121 = bn256_fr_to_args(f.0.c1.c2.c1, ForeignInst::Bn254PairG3);
        vec![
            c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121,
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn bn256_g1_to_args(g: G1, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let g_af = G1Affine::from(g);
        let mut a = bn256_fr_to_args(g_af.x, op);
        let mut b = bn256_fr_to_args(g_af.y, op);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        a.append(&mut b);
        a.append(&mut vec![ExternalHostCallEntry {
            op: op as usize,
            value: z,
            is_ret: false,
        }]);
        a
    }

    fn bn256_g2_to_pair_args(g: G2) -> Vec<ExternalHostCallEntry> {
        let g_af = G2Affine::from(g);
        let x0 = bn256_fr_to_args(g_af.x.c0, ForeignInst::Bn254PairG2);
        let x1 = bn256_fr_to_args(g_af.x.c1, ForeignInst::Bn254PairG2);
        let y0 = bn256_fr_to_args(g_af.y.c0, ForeignInst::Bn254PairG2);
        let y1 = bn256_fr_to_args(g_af.y.c1, ForeignInst::Bn254PairG2);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        let zentry = ExternalHostCallEntry {
            op: ForeignInst::Bn254PairG2 as usize,
            value: z,
            is_ret: false,
        };
        vec![x0, x1, y0, y1, vec![zentry]]
            .into_iter()
            .flatten()
            .collect()
    }

    fn create_bn256_pair_shared_table(a: G1, b: G2) -> ExternalHostCallEntryTable {
        let a_af = G1Affine::from(a);
        let b_af = G2Affine::from(b);
        let ab: Bn256Gt = pairing(&a_af, &b_af);
        let g1_args = bn256_g1_to_args(a, ForeignInst::Bn254PairG1);
        let g2_args = bn256_g2_to_pair_args(b);
        let ab_args = bn256_gt_to_pair_args(ab);
        let table = ExternalHostCallEntryTable(
            vec![g1_args, g2_args, ab_args]
                .into_iter()
                .flatten()
                .collect(),
        );
        table
    }

    fn create_bn256_sum_shared_table(ls: Vec<G1>, sum: G1) -> ExternalHostCallEntryTable {
        let mut r = ls
            .iter()
            .map(|x| bn256_g1_to_args(x.clone(), ForeignInst::Bn254SumG1))
            .flatten()
            .collect::<Vec<ExternalHostCallEntry>>();
        r.append(&mut bn256_g1_to_args(
            sum.clone(),
            ForeignInst::Bn254SumResult,
        ));
        ExternalHostCallEntryTable(r)
    }
    #[test]
    fn generate_bn256_pair_input() {
        let a = G1::random(&mut OsRng);
        let b = G2::random(&mut OsRng);
        let table = create_bn256_pair_shared_table(a, b);
        let file = File::create("bn256pairtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_bn256_sum_input() {
        let mut inputs = vec![];
        for _ in 0..2 {
            inputs.insert(0, G1::random(&mut OsRng).into());
        }
        let ret = inputs[1..2]
            .into_iter()
            .fold(inputs[0], |acc: G1, x| acc.add(x.clone()));

        let table = create_bn256_sum_shared_table(inputs, ret);
        let file = File::create("bn256sumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
