use super::{ExternalHostCallEntry, ExternalHostCallEntryTable};

use crate::utils::field_to_bn;
use num_bigint::BigUint;
use std::ops::Shl;
use halo2_proofs::pairing::bls12_381::{G1Affine, G2Affine,
    Gt as Bls381Gt,
    Fq as Bls381Fq
};
use halo2_proofs::pairing::bls12_381::pairing;


fn bls381_fr_to_pair_args(f: Bls381Fq, is_ret: bool) -> Vec<ExternalHostCallEntry> {
    let mut bn = field_to_bn(&f);
    let mut ret = vec![];
    for _ in 0..8 {
        let d:BigUint = BigUint::from(1u64 << 54);
        let r = bn.clone() % d.clone();
        let value = if r == BigUint::from(0 as u32) {
            0 as u64
        } else {
            r.to_u64_digits()[0]
        };
        println!("d is {:?}, remainder is {:?}", d, r);
        bn = bn / d;
        let entry = ExternalHostCallEntry {
            op: 1,
            value,
            is_ret,
        };
        ret.append(&mut vec![entry]);
    };
    ret
}

fn bls381_gt_to_pair_args(f: Bls381Gt) -> Vec<ExternalHostCallEntry> {
    let c000 = bls381_fr_to_pair_args(f.0.c0.c0.c0, true);
    let c001 = bls381_fr_to_pair_args(f.0.c0.c0.c1, true);
    let c010 = bls381_fr_to_pair_args(f.0.c0.c1.c0, true);
    let c011 = bls381_fr_to_pair_args(f.0.c0.c1.c1, true);
    let c020 = bls381_fr_to_pair_args(f.0.c0.c2.c0, true);
    let c021 = bls381_fr_to_pair_args(f.0.c0.c2.c1, true);
    let c100 = bls381_fr_to_pair_args(f.0.c1.c0.c0, true);
    let c101 = bls381_fr_to_pair_args(f.0.c1.c0.c1, true);
    let c110 = bls381_fr_to_pair_args(f.0.c1.c1.c0, true);
    let c111 = bls381_fr_to_pair_args(f.0.c1.c1.c1, true);
    let c120 = bls381_fr_to_pair_args(f.0.c1.c2.c0, true);
    let c121 = bls381_fr_to_pair_args(f.0.c1.c2.c1, true);
    vec![c000, c001, c010, c011, c020, c021, c100, c101, c110, c111, c120, c121].into_iter().flatten().collect()
}

fn bls381_g1_to_pair_args(g:G1Affine) -> Vec<ExternalHostCallEntry> {
    let mut a = bls381_fr_to_pair_args(g.x, false);
    let mut b = bls381_fr_to_pair_args(g.y, false);
    let z:u64 = g.is_identity().unwrap_u8() as u64;
    a.append(&mut b);
    a.append(&mut vec![ExternalHostCallEntry{
        op:1,
        value: z,
        is_ret:false,
    }]);
    a
}

fn bls381_g2_to_pair_args(g:G2Affine) -> Vec<ExternalHostCallEntry> {
    let x0 = bls381_fr_to_pair_args(g.x.c0, false);
    let x1 = bls381_fr_to_pair_args(g.x.c1, false);
    let y0 = bls381_fr_to_pair_args(g.y.c0, false);
    let y1 = bls381_fr_to_pair_args(g.y.c1, false);
    let z:u64 = g.is_identity().unwrap_u8() as u64;
    let zentry = ExternalHostCallEntry{
        op:1,
        value: z,
        is_ret:false,
    };
    vec![x0,x1,y0,y1, vec![zentry]].into_iter().flatten().collect()
}

pub fn create_shared_table(a: G1Affine, b: G2Affine) -> ExternalHostCallEntryTable {
    let ab:Bls381Gt = pairing(&a, &b);
    let g1_args = bls381_g1_to_pair_args(a);
    let g2_args = bls381_g2_to_pair_args(b);
    let ab_args = bls381_gt_to_pair_args(ab);
    let table = ExternalHostCallEntryTable (
        vec![g1_args, g2_args, ab_args].into_iter().flatten().collect()
    );
    table
}

#[cfg(test)]
mod tests {
    use rand::rngs::OsRng;
    use crate::host::bls::create_shared_table;
    use std::fs::File;
    use halo2_proofs::pairing::bls12_381::{
        G1Affine,
        G2Affine,
        G1, G2,
    };

    use halo2_proofs::pairing::group::Group;

    #[test]
    fn generate_bls_input() {
        let a:G1Affine = G1::random(&mut OsRng).into();
        let b:G2Affine = G2Affine::from(G2::random(&mut OsRng));
        let table = create_shared_table(a, b);
        let file = File::create("blstest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
        /* todo: output to blstest.json */
    }
}
