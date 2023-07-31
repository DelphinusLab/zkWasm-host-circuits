use crate::utils::bn_to_field;
use ff::Field;
use halo2_proofs::pairing::bn256::Fr;
use lazy_static::lazy_static;
use num_bigint::BigUint;
use std::ops::{AddAssign, MulAssign, SubAssign};

lazy_static! {
    static ref D_BIG: BigUint = BigUint::parse_bytes(
        b"12181644023421730124874158521699555681764249180949974110617291017600649128846",
        10
    )
    .unwrap();
    static ref D: Fr = bn_to_field(&(D_BIG));
    static ref A_BIG: BigUint = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495616",
        10
    )
    .unwrap();
    static ref A: Fr = bn_to_field(&(A_BIG));
    pub static ref Q: BigUint = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10
    )
    .unwrap();
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
        b = b.square();
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


    #[allow(clippy::many_single_char_names)]
    pub fn double(&self) -> PointProjective {
        // dbl-2008-bbjlp https://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html#dbl-2008-bbjlp
        let mut two = Fr::one();
        two = two.double();

        let mut b = self.x;
        b.add_assign(&self.y);
        b = b.square();

        let mut c = self.x;
        c = c.square();

        let mut d = self.y;
        d = d.square();

        let mut e = *A;
        e.mul_assign(&c);

        let mut f = e;
        f.add_assign(&d);

        let mut h = self.z;
        h = h.square();

        let mut h2 = two;
        h2.mul_assign(&h);

        let mut j = f;
        j.sub_assign(&h2);

        let mut x3 = b;
        x3.sub_assign(&c);
        x3.sub_assign(&d);
        x3.mul_assign(&j);

        let mut ed = e;
        ed.sub_assign(&d);
        let mut y3 = f;
        // y3.sub_assign(d);
        y3.mul_assign(&ed);

        let mut z3 = f;
        z3.mul_assign(&j);
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

    pub fn add(&self, other: &Point) -> Point {
        self.projective().add(&other.projective()).affine()
    }

    pub fn mul_scalar(&self, n: &BigUint) -> Point {
        let mut r = Point::identity().projective();
        let mut exp = self.projective();
        let b = n.to_bytes_le();
        //little-end wise, like 6, it is 0,1,1 sequence
        for i in 0..n.bits() {
            if test_bit(&b, i.try_into().unwrap()) {
                r = r.add(&exp);
            }
            exp = exp.double();
        }
        r.affine()
    }
}

pub fn test_bit(b: &[u8], i: usize) -> bool {
    b[i / 8] & (1 << (i % 8)) != 0
}

#[cfg(test)]
mod tests {
    use super::Point;
    use crate::utils::bn_to_field;
    use crate::utils::field_to_bn;
    use halo2_proofs::pairing::bn256::Fr;
    use num_bigint::BigUint;
    use std::str::FromStr;
    #[test]
    pub fn verify_alt_jubjub_signature() {
        let msg = "12183188902842291436925829409440956230535359139686694837527706100765491669070";

        let pk_x = BigUint::parse_bytes(
            b"252e5567f8d2ec21093deb668196ebd676767e5414d167a09223d72a354e5b45",
            16,
        )
        .unwrap();
        let pk_y = BigUint::parse_bytes(
            b"2e91ef67e1f4bad22d03af787175c1ddeeca18c59451421a3958c6b64a376ec4",
            16,
        )
        .unwrap();
        let pk = Point {
            x: bn_to_field(&pk_x),
            y: bn_to_field(&pk_y),
        };

        println!("pk_x is: {:?} {:?}", BigUint::to_u64_digits(&pk_x), pk_x);
        println!("pk_y is: {:?} {:?}", BigUint::to_u64_digits(&pk_y), pk_y);

        let sig_rx = BigUint::parse_bytes(
            b"03871ac3f0ae73813b0a4bbaa778bd0ea3d43d75297cd1a2d3a8b98e053cf2af",
            16,
        )
        .unwrap();
        let sig_ry = BigUint::parse_bytes(
            b"1054763a3bdce693bb5f58064092cb5d3f45473eda5f1d0ead04e9e3a7b278f7",
            16,
        )
        .unwrap();

        let sig_r = Point {
            x: bn_to_field(&sig_rx),
            y: bn_to_field(&sig_ry),
        };

        println!(
            "sig_rx is: {:?} {:?}",
            BigUint::to_u64_digits(&sig_rx),
            sig_rx
        );
        println!(
            "sig_ry is: {:?} {:?}",
            BigUint::to_u64_digits(&sig_ry),
            sig_ry
        );

        // let p_g = Point {
        //     x: bn_to_field(&(BigUint::parse_bytes(b"2ef3f9b423a2c8c74e9803958f6c320e854a1c1c06cd5cc8fd221dc052d76df7", 16).unwrap())),
        //     y: bn_to_field(&(BigUint::parse_bytes(b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7", 16).unwrap())),
        // };

        //p_g.negate()
        let base_x = BigUint::parse_bytes(
            b"017054bebd8ed76269b84220f215264ea2e9cc2c72ec13c846bfd7d39d28920a",
            16,
        )
        .unwrap();
        let base_y = BigUint::parse_bytes(
            b"05a01167ea785d3f784224644a68e4067532c815f5f6d57d984b5c0e9c6c94b7",
            16,
        )
        .unwrap();
        let p_g_neg = Point {
            x: bn_to_field(&(base_x)),
            y: bn_to_field(&(base_y)),
        };
        let sig_s_str =
            "760414664615846567287977379644619164343552866248912558409257763292500819717";

        println!(
            "base x is: {:?} {:?}",
            BigUint::to_u64_digits(&base_x),
            BigUint::to_u64_digits(&field_to_bn(&-bn_to_field::<Fr>(&base_x)))
        );
        println!(
            "base y is: {:?} {:?}",
            BigUint::to_u64_digits(&base_y),
            base_y
        );

        let c = BigUint::from_str(msg).unwrap();
        let sig_s = BigUint::from_str(sig_s_str).unwrap();

        // Do not remove following prints as they are used in zkwasm sdk tests
        println!("msghash is {:?}", BigUint::to_u64_digits(&c));
        println!("sig_s is {:?}, {:?}", BigUint::to_u64_digits(&sig_s), sig_s);

        // 0 = c . vk + R -S . P_G that requires all points to be in the same group
        let lhs = pk.mul_scalar(&c);
        println!("first round {:?}", lhs);
        let lhs = lhs.add(&sig_r);
        println!("second round {:?}", lhs);
        let rhs = p_g_neg.mul_scalar(&sig_s);
        let rst = lhs.add(&rhs);
        println!("third round {:?}", rst);
        // assert_eq!(lhs,rhs)
        assert_eq!(Point::identity(),rst);
    }
}
