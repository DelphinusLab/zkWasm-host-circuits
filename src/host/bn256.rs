#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::utils::field_to_bn;
    use halo2_proofs::pairing::bn256::pairing;
    use halo2_proofs::pairing::bn256::Fr;
    use ff::Field;
    use halo2_proofs::pairing::bn256::{Fq as Bn256Fq, G1Affine, G2Affine, Gt as Bn256Gt, G1, G2};
    use halo2_proofs::pairing::group::Group;
    use num_bigint::BigUint;
    use rand::rngs::OsRng;
    use std::fs::File;
    use std::ops::Add;

    fn bn256_fr_to_args(f: Fr, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut bn = field_to_bn(&f);
        let mut ret = vec![];
        for _ in 0..4 {
            let d: BigUint = BigUint::from(1u128 << 64);
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

    fn bn256_fq_to_args(f: Bn256Fq, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
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
        let c000 = bn256_fq_to_args(f.0.c0.c0.c0, ForeignInst::Bn254PairG3);
        let c001 = bn256_fq_to_args(f.0.c0.c0.c1, ForeignInst::Bn254PairG3);
        let c010 = bn256_fq_to_args(f.0.c0.c1.c0, ForeignInst::Bn254PairG3);
        let c011 = bn256_fq_to_args(f.0.c0.c1.c1, ForeignInst::Bn254PairG3);
        let c020 = bn256_fq_to_args(f.0.c0.c2.c0, ForeignInst::Bn254PairG3);
        let c021 = bn256_fq_to_args(f.0.c0.c2.c1, ForeignInst::Bn254PairG3);
        let c100 = bn256_fq_to_args(f.0.c1.c0.c0, ForeignInst::Bn254PairG3);
        let c101 = bn256_fq_to_args(f.0.c1.c0.c1, ForeignInst::Bn254PairG3);
        let c110 = bn256_fq_to_args(f.0.c1.c1.c0, ForeignInst::Bn254PairG3);
        let c111 = bn256_fq_to_args(f.0.c1.c1.c1, ForeignInst::Bn254PairG3);
        let c120 = bn256_fq_to_args(f.0.c1.c2.c0, ForeignInst::Bn254PairG3);
        let c121 = bn256_fq_to_args(f.0.c1.c2.c1, ForeignInst::Bn254PairG3);
        vec![
            c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121,
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn bn256_g1_to_args(g: G1, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let g_af = G1Affine::from(g);
        let mut a = bn256_fq_to_args(g_af.x, op);
        let mut b = bn256_fq_to_args(g_af.y, op);
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
        let x0 = bn256_fq_to_args(g_af.x.c0, ForeignInst::Bn254PairG2);
        let x1 = bn256_fq_to_args(g_af.x.c1, ForeignInst::Bn254PairG2);
        let y0 = bn256_fq_to_args(g_af.y.c0, ForeignInst::Bn254PairG2);
        let y1 = bn256_fq_to_args(g_af.y.c1, ForeignInst::Bn254PairG2);
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

    fn create_bn256_sum_input(new: u32, a: Fr, g: G1, sum: G1) -> Vec<ExternalHostCallEntry> {
        let mut r = vec![];
        r.append(&mut vec![ExternalHostCallEntry {
            op: ForeignInst::Bn254SumNew as usize,
            value: new as u64,
            is_ret: false,
        }]);
        r.append(&mut bn256_fr_to_args(a, ForeignInst::Bn254SumScalar));
        r.append(&mut bn256_g1_to_args(g, ForeignInst::Bn254SumG1));
        r.append(&mut bn256_g1_to_args(sum, ForeignInst::Bn254SumResult));
        r
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
        let l = [2, 4, 3];
        let mut inputs = vec![];
        for i in 0..3 {
            let mut z = G1::identity();
            for j in 0..l[i] {
                let new = if j == 0 {1} else {0};
                let a_j = Fr::random(&mut OsRng);
                let g_j = G1::random(&mut OsRng);
                let r = g_j * a_j;
                z = z.add(r.clone());
                inputs.append(&mut create_bn256_sum_input(new, a_j, g_j, z));
            }
        }
        let table = ExternalHostCallEntryTable(inputs);
        let file = File::create("bn256sumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
