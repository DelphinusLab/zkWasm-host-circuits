use lazy_static::lazy_static;
use crate::utils::bn_to_field;
use halo2_proofs::pairing::bn256::Fr;
use std::ops::{SubAssign, MulAssign, AddAssign};
use ff::Field;
use ff::PrimeField;
use num_bigint::BigUint;

lazy_static! {
    static ref D_BIG: BigUint = BigUint::parse_bytes(b"168696", 10).unwrap();
    static ref D: Fr = bn_to_field(&(D_BIG));
    static ref A_BIG: BigUint = BigUint::parse_bytes(b"168700", 10).unwrap();
    static ref A: Fr = bn_to_field(&(A_BIG));
    pub static ref Q: BigUint = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",10
    ).unwrap();
}

#[derive(Clone, Debug)]
pub struct PointProjective {
    pub x: Fr,
    pub y: Fr,
    pub z: Fr,
}

impl PointProjective {
    pub fn affine(&self) -> Point {
        if self.z.is_zero_vartime() {
            return Point {
                x: Fr::zero(),
                y: Fr::zero(),
            };
        }

        let zinv = self.z.invert().unwrap();
        let mut x = self.x;
        x.mul_assign(&zinv);
        let mut y = self.y;
        y.mul_assign(&zinv);

        Point { x, y }
    }

    #[allow(clippy::many_single_char_names)]
    pub fn add(&self, q: &PointProjective) -> PointProjective {
        // add-2008-bbjlp https://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#addition-add-2008-bbjlp
        let mut a = self.z;
        a.mul_assign(&q.z);
        let mut b = a;
        b.square();
        let mut c = self.x;
        c.mul_assign(&q.x);
        let mut d = self.y;
        d.mul_assign(&q.y);
        let mut e = *D;
        e.mul_assign(&c);
        e.mul_assign(&d);
        let mut f = b;
        f.sub_assign(&e);
        let mut g = b;
        g.add_assign(&e);
        let mut x1y1 = self.x;
        x1y1.add_assign(&self.y);
        let mut x2y2 = q.x;
        x2y2.add_assign(&q.y);
        let mut aux = x1y1;
        aux.mul_assign(&x2y2);
        aux.sub_assign(&c);
        aux.sub_assign(&d);
        let mut x3 = a;
        x3.mul_assign(&f);
        x3.mul_assign(&aux);
        let mut ac = *A;
        ac.mul_assign(&c);
        let mut dac = d;
        dac.sub_assign(&ac);
        let mut y3 = a;
        y3.mul_assign(&g);
        y3.mul_assign(&dac);
        let mut z3 = f;
        z3.mul_assign(&g);

        PointProjective {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Point {
    pub x: Fr,
    pub y: Fr,
}

impl Point {
    pub fn identity() -> Self {
        Point {
            x: Fr::zero(),
            y: Fr::one(),
        }
    }
    pub fn projective(&self) -> PointProjective {
        PointProjective {
            x: self.x,
            y: self.y,
            z: Fr::one(),
        }
    }

    pub fn mul_scalar(&self, n: &BigUint) -> Point {
        let mut r: PointProjective = PointProjective {
            x: Fr::zero(),
            y: Fr::one(),
            z: Fr::one(),
        };
        let mut exp: PointProjective = self.projective();
        let b = n.to_bytes_le();
        for i in 0..n.bits() {
            if test_bit(&b, i.try_into().unwrap()) {
                r = r.add(&exp);
            }
            exp = exp.add(&exp);
        }
        r.affine()
    }
}

pub fn test_bit(b: &[u8], i: usize) -> bool {
    b[i / 8] & (1 << (i % 8)) != 0
}

#[cfg(test)]

mod tests {
    use crate::host::{ExternalHostCallEntry, ExternalHostCallEntryTable, ForeignInst};
    use crate::utils::field_to_bn;
    use crate::adaptor::fr_to_args;
    use halo2_proofs::arithmetic::FieldExt;
    use halo2_proofs::pairing::bn256::pairing;
    use halo2_proofs::pairing::bn256::Fr;
    use halo2_proofs::pairing::group::Group;
    use super::{Point, PointProjective};
    use num_bigint::BigUint;
    use rand::rngs::OsRng;
    use std::fs::File;
    use std::ops::Add;


    fn babyarg_to_args(v: &Fr, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
        fr_to_args(*v, 4, 64, op)
    }

    fn babysum_to_args(x: Point, y: Point, z:Point) -> Vec<ExternalHostCallEntry> {
        let mut ret = vec![
            babyarg_to_args(&x.x, ForeignInst::JubjubSumPush),
            babyarg_to_args(&x.y, ForeignInst::JubjubSumPush),
            babyarg_to_args(&y.x, ForeignInst::JubjubSumPush),
            babyarg_to_args(&y.y, ForeignInst::JubjubSumPush),
            babyarg_to_args(&z.x, ForeignInst::JubjubSumResult),
            babyarg_to_args(&z.y, ForeignInst::JubjubSumResult)
        ]
        .into_iter()
        .flatten()
        .collect();
        ret
    }

    struct JubjubSumContext {
        acc: Point,
        operand: Point,
        coeff: [u64; 4],
    }

    fn generate_entries_single_round(context: &mut JubjubSumContext)  -> Vec<ExternalHostCallEntry> {
        todo!()
    }

    #[test]
    fn generate_jubjub_sum_input() {
        let identity = Point::identity();
        let identity_proj = identity.projective();
        let entries = babysum_to_args(Point::identity(), Point::identity(), identity_proj.add(&identity_proj).affine());
        let table = ExternalHostCallEntryTable(entries);
        let file = File::create("jubjubsumtest.json").expect("can not create file");
        serde_json::to_writer_pretty(file, &table).expect("can not write to file");
        assert_eq!(identity, identity_proj.add(&identity_proj).affine());
    }
}
