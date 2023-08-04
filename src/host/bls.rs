#[cfg(test)]
mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::utils::field_to_bn;
    use halo2_proofs::pairing::bls12_381::pairing;
    use ff::Field;
    use halo2_proofs::pairing::bls12_381::{
        Fq as Bls381Fq, G1Affine, G2Affine, Gt as Bls381Gt, G1, G2, Fr
    };
    use halo2_proofs::pairing::group::Group;
    use num_bigint::BigUint;
    use rand::rngs::OsRng;
    use std::fs::File;
    use std::ops::Add;

    fn bls381_fr_to_args(f: Fr, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
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

    fn bls381_fq_to_args(f: Bls381Fq, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut bn = field_to_bn(&f);
        let mut ret = vec![];
        for _ in 0..8 {
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

    fn bls381_gt_to_pair_args(f: Bls381Gt) -> Vec<ExternalHostCallEntry> {
        let c000 = bls381_fq_to_args(f.0.c0.c0.c0, ForeignInst::BlsPairG3);
        let c001 = bls381_fq_to_args(f.0.c0.c0.c1, ForeignInst::BlsPairG3);
        let c010 = bls381_fq_to_args(f.0.c0.c1.c0, ForeignInst::BlsPairG3);
        let c011 = bls381_fq_to_args(f.0.c0.c1.c1, ForeignInst::BlsPairG3);
        let c020 = bls381_fq_to_args(f.0.c0.c2.c0, ForeignInst::BlsPairG3);
        let c021 = bls381_fq_to_args(f.0.c0.c2.c1, ForeignInst::BlsPairG3);
        let c100 = bls381_fq_to_args(f.0.c1.c0.c0, ForeignInst::BlsPairG3);
        let c101 = bls381_fq_to_args(f.0.c1.c0.c1, ForeignInst::BlsPairG3);
        let c110 = bls381_fq_to_args(f.0.c1.c1.c0, ForeignInst::BlsPairG3);
        let c111 = bls381_fq_to_args(f.0.c1.c1.c1, ForeignInst::BlsPairG3);
        let c120 = bls381_fq_to_args(f.0.c1.c2.c0, ForeignInst::BlsPairG3);
        let c121 = bls381_fq_to_args(f.0.c1.c2.c1, ForeignInst::BlsPairG3);
        vec![
            c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121,
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    fn bls381_g1_to_args(g: G1Affine, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        let mut a = bls381_fq_to_args(g.x, op);
        let mut b = bls381_fq_to_args(g.y, op);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        a.append(&mut b);
        a.append(&mut vec![ExternalHostCallEntry {
            op: op as usize,
            value: z,
            is_ret: false,
        }]);
        a
    }

    fn bls381_g2_to_pair_args(g: G2Affine) -> Vec<ExternalHostCallEntry> {
        let x0 = bls381_fq_to_args(g.x.c0, ForeignInst::BlsPairG2);
        let x1 = bls381_fq_to_args(g.x.c1, ForeignInst::BlsPairG2);
        let y0 = bls381_fq_to_args(g.y.c0, ForeignInst::BlsPairG2);
        let y1 = bls381_fq_to_args(g.y.c1, ForeignInst::BlsPairG2);
        let z: u64 = g.is_identity().unwrap_u8() as u64;
        let zentry = ExternalHostCallEntry {
            op: ForeignInst::BlsPairG2 as usize,
            value: z,
            is_ret: false,
        };
        vec![x0, x1, y0, y1, vec![zentry]]
            .into_iter()
            .flatten()
            .collect()
    }

    pub fn create_bls_pair_shared_table(a: G1Affine, b: G2Affine) -> ExternalHostCallEntryTable {
        let ab: Bls381Gt = pairing(&a, &b);
        let g1_args = bls381_g1_to_args(a, ForeignInst::BlsPairG1);
        let g2_args = bls381_g2_to_pair_args(b);
        let ab_args = bls381_gt_to_pair_args(ab);
        let table = ExternalHostCallEntryTable(
            vec![g1_args, g2_args, ab_args]
                .into_iter()
                .flatten()
                .collect(),
        );
        table
    }

    fn create_bls_sum_input(new: u32, a: Fr, g: G1Affine, sum: G1Affine) -> Vec<ExternalHostCallEntry> {
        let mut r = vec![];
        r.append(&mut vec![ExternalHostCallEntry {
            op: ForeignInst::BlsSumNew as usize,
            value: new as u64,
            is_ret: false,
        }]);
        r.append(&mut bls381_fr_to_args(a, ForeignInst::BlsSumScalar));
        r.append(&mut bls381_g1_to_args(g, ForeignInst::BlsSumG1));
        r.append(&mut bls381_g1_to_args(sum, ForeignInst::BlsSumResult));
        r
    }

    #[test]
    fn generate_bls_pair_input() {
        let a: G1Affine = G1::random(&mut OsRng).into();
        let b: G2Affine = G2Affine::from(G2::random(&mut OsRng));
        let table = create_bls_pair_shared_table(a, b);
        let file = File::create("blspairtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }

    #[test]
    fn generate_bls_sum_input() {
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
                inputs.append(&mut create_bls_sum_input(new, a_j, G1Affine::from(g_j), G1Affine::from(z)));
            }
        }
        let table = ExternalHostCallEntryTable(inputs);
        let file = File::create("blssumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
    }
}
