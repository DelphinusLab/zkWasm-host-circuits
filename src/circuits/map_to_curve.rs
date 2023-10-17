#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused)]

/// Circuit to constrain the map to curve function, which takes
/// as an input an element of Fq2 and outputs a point on the elliptic curve.
/// (TODO: more details)
/// 
/// Note 1: The reference document uses p for the characteristic of the
/// field.  Our structs refer to the same prime as q: for example, 
/// `AssignedFq`.
/// 
/// The suffixes "_bn", "_fq", "_fq2" indicate that a variable is a
/// BigUint, element of Fq, or element of Fq2, respectively.
/// A variable without one of these suffixes is assumed to be an
/// AssignedFq2<Fq, Fr>, which is the representation of an element of Fq2
/// in the computation trace (Context).

use halo2ecc_s::assign::{AssignedFq, AssignedFq2};
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::circuit::fq12::Fq2ChipOps;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::context::*;
use halo2ecc_s::utils::*;
use halo2_proofs::pairing::bls12_381::{G1Affine, Fq};
use halo2_proofs::pairing::bn256::{Fr, G1};
use num_bigint::BigUint;
use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;

// Assigns e = (a == b) within the computation trace (Context),
// where a and b are elements of Fq2.  In the same computation trace,
// e is also an element of Fq2, which is constrained so that
// e == 1 = 1 + 0i = (1, 0) if and only if a == b, and
// e == 0 = 0 + 0i = (0, 0) if and only if a != b.
fn fq2_assign_equality_condition(
    gseccc: &mut GeneralScalarEccContext::<G1Affine, Fr>,
    a: &AssignedFq2::<Fq, Fr>,
    b: &AssignedFq2::<Fq, Fr>,
) -> AssignedFq2::<Fq, Fr> {
    let a_minus_b: AssignedFq2<Fq, Fr> = gseccc.fq2_sub(&a, &b);

    // First, give the prover instructions on how to assign inv0(a - b),
    // without constraining.  In the notation of the reference document,
    // inv0(x) = x^{-1} if x is invertible, 0 otherwise.
    let a_re_fq = gseccc.base_integer_ctx.get_w(&a.0);
    let a_im_fq = gseccc.base_integer_ctx.get_w(&a.1);
    let b_re_fq = gseccc.base_integer_ctx.get_w(&b.0);
    let b_im_fq = gseccc.base_integer_ctx.get_w(&b.1);
    let a_equals_b = (a_re_fq == b_re_fq) && (a_im_fq == b_im_fq);
    
    // Here we are using assign_w instead of assign_zero because assign_zero 
    // is a special cases of assign_constant.  But e depends on prover input, 
    // and so is not a constant in the computation trace or circuit.
    let a_minus_b_inv0: AssignedFq2<Fq, Fr> = if a_equals_b {
        let zero_bn = BigUint::from_str("0").unwrap();
        (
            gseccc.base_integer_ctx.assign_w(&zero_bn),
            gseccc.base_integer_ctx.assign_w(&zero_bn),
            
        )
    } else {
        // Since fq2_unsafe_invert may introduce additional constraints,
        // we do not use it here, as the constraints should not depend on
        // the prover input.
        let a_minus_b_re_fq = a_re_fq - b_re_fq;
        let a_minus_b_im_fq = a_im_fq - b_im_fq;
        let a_minus_b_norm_squared_fq = (a_minus_b_re_fq * a_minus_b_re_fq.clone()) + (a_minus_b_im_fq * a_minus_b_im_fq.clone());
        let a_minus_b_norm_squared_inverse_fq = a_minus_b_norm_squared_fq.invert().unwrap();
        let a_minus_b_inv0_re_fq: Fq = a_minus_b_re_fq * a_minus_b_norm_squared_inverse_fq;
        let a_minus_b_inv0_im_fq: Fq = -a_minus_b_im_fq * a_minus_b_norm_squared_inverse_fq.clone();
        let a_minus_b_inv0_re_bn = field_to_bn(&a_minus_b_inv0_re_fq);
        let a_minus_b_inv0_im_bn = field_to_bn(&a_minus_b_inv0_im_fq);
        (
            gseccc.base_integer_ctx.assign_w(&a_minus_b_inv0_re_bn),
            gseccc.base_integer_ctx.assign_w(&a_minus_b_inv0_im_bn),
        )
    };

    // Note that for field elements s and t, t^2 * s = t if and only if 
    // either t = 0 or s = t^{-1}.  Therefore the following constraints
    // enforce that a_minus_b_inv0 = (a_minus_b)^{-1} if a - b != 0;
    // otherwise, a_minus_b_inv0 is unconstrained.
    let a_minus_b_squared: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&a_minus_b);
    let a_minus_b_squared_times_a_minus_b_inv0: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&a_minus_b_squared, &a_minus_b_inv0);
    gseccc.fq2_assert_equal(&a_minus_b_squared_times_a_minus_b_inv0, &a_minus_b);

    // Now that we've constrained a_minus_b_inv0 this way, it follows that
    // a_minus_b * a_minus_b_inv0 = 0 if a_minus_b = 0, 1 otherwise.
    // In other words, a_minus_b * a_minus_b_inv0 = !(a_minus_b == 0)
    let not_e: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&a_minus_b, &a_minus_b_inv0);
    let one: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_one();
    let e: AssignedFq2<Fq, Fr> = gseccc.fq2_sub(&one, &not_e);

    e
}

fn cmov(
    gseccc: &mut GeneralScalarEccContext::<G1Affine, Fr>,
    a: &AssignedFq2::<Fq, Fr>,
    b: &AssignedFq2::<Fq, Fr>,
    e: &AssignedFq2::<Fq, Fr>,
) -> AssignedFq2::<Fq, Fr> {
    let one: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_one();
    let not_e: AssignedFq2<Fq, Fr> = gseccc.fq2_sub(&one, e);
    let not_e_times_a: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&not_e, a);
    let e_times_b: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(e, &b);
    let not_e_times_a_plus_e_times_b: AssignedFq2<Fq, Fr> = gseccc.fq2_add(&not_e_times_a, &e_times_b);

    not_e_times_a_plus_e_times_b
}

// Only for testing purposes; actual sgn0 must be constrained.
fn sgn0_unconstrained(
    gseccc: &mut GeneralScalarEccContext::<G1Affine, Fr>,
    u: &AssignedFq2::<Fq, Fr>,
) -> usize {
    let u_re_fq = gseccc.base_integer_ctx.get_w(&u.0);
    let u_im_fq = gseccc.base_integer_ctx.get_w(&u.1);
    let u_re_bn = field_to_bn(&u_re_fq);
    let u_im_bn = field_to_bn(&u_im_fq);

    let zero_bn = BigUint::from_str("0").unwrap();
    let one_bn = BigUint::from_str("1").unwrap();
    let two_bn = BigUint::from_str("2").unwrap();

    let u_re_bn_parity = &u_re_bn % &two_bn;
    let u_im_bn_parity = &u_im_bn % &two_bn;

    let sign_0_equals_1 = u_re_bn_parity == one_bn || (u_re_bn == zero_bn && u_im_bn_parity == one_bn);
    let sign_0: usize = if sign_0_equals_1 { 1 } else { 0 };

    sign_0
}

fn simplified_swu_in_context(
    gseccc: &mut GeneralScalarEccContext::<G1Affine, Fr>,
    u: &AssignedFq2<Fq, Fr>,
) -> (AssignedFq2<Fq, Fr>, AssignedFq2<Fq, Fr>) {
    /// Constants: see Section 8.8.2 of https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-09 
    /// Although these are constants in the mathematical sense, the compiler
    /// will not allow me to make these constants in the Rust sense.  But they
    /// are immutable, which is the next best thing.
    /// 
    /// Z = -(2 + i)
    /// A' = 240i
    /// B' = 1012 + 1012i
    /// 
    /// Note: c1 is an integer, and not a field element.  We will hard-code
    /// into the circuit the square-and-multiply algorithm specific to taking
    /// a field element to the power of c1.  Thus in the code we need to write
    /// c1 in binary.  For reference, we write it here in hexadecimal.
    /// c1 = (p^2 - 9)/16 = 0x2a437a4b8c35fc74bd278eaa22f25e9e2dc90e50e7046b466e59e49349e8bd050a62cfd16ddca6ef53149330978ef011d68619c86185c7b292e85a87091a04966bf91ed3e71b743162c338362113cfd7ced6b1d76382eab26aa00001c718e3
    /// c2 = sqrt(-1) = i
    /// c3 = sqrt(c2) = 0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2 + (0x06af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09)i
    /// c4 = 0x136753aead177603ecbfaf2395ee800fb38ef1737f8232e72bb1880c78ae1cabd529aa5c0667f539924950420e408e1b + (0x11eb95120939a15aed4b108ad51262f33bf72acf3adb46259d28f0306d0e27ffe7d29afc46792c103e535c80de7bc0f6)i
    /// c5 = 0x0f5d0d63d2797471e6d39f306cc0dc0ab85de3bd9f39ce46f3649ac0de9e844417cc8de88716c1fd323fa68040801aea + (0x0ab1c2ffdd6c253ca155231eb3e71ba044fd562f6f72bc5bad5ec46a0b7a3b0247cf08ce6c6317f40edbc653a72dee17)i
    
    // Z = -(2 + i)
    let z_fq2 = (-(Fq::one() + Fq::one()), -Fq::one());
    let z: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(z_fq2);

    // A' = 240i
    let a_prime_re_fq = Fq::zero();
    let a_prime_im_bn = BigUint::from_str("240").unwrap();
    let a_prime_im_fq: Fq = bn_to_field(&a_prime_im_bn);
    let a_prime_fq2 = (a_prime_re_fq, a_prime_im_fq);
    let a_prime: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(a_prime_fq2);

    // B' = 1012 + 1012i
    let b_prime_re_bn = BigUint::from_str("1012").unwrap();
    let b_prime_re_fq: Fq = bn_to_field(&b_prime_re_bn);
    let b_prime_im_fq = b_prime_re_fq.clone();
    let b_prime_fq2 = (b_prime_re_fq, b_prime_im_fq);
    let b_prime: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(b_prime_fq2);

    // c1 in binary
    let c1_str = "10101001000011011110100100101110001100001101011111110001110100101111010010011110001110101010100010001011110010010111101001111000101101110010010000111001010000111001110000010001101011010001100110111001011001111001001001001101001001111010001011110100000101000010100110001011001111110100010110110111011100101001101110111101010011000101001001001100110000100101111000111011110000000100011101011010000110000110011100100001100001100001011100011110110010100100101110100001011010100001110000100100011010000001001001011001101011111110010001111011010011111001110001101101110100001100010110001011000011001110000011011000100001000100111100111111010111110011101101011010110001110101110110001110000010111010101011001001101010101000000000000000000001110001110001100011100011";

    // c2 = i
    let c2_fq2: (Fq, Fq) = (Fq::zero(), Fq::one());
    let c2: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(c2_fq2);

    // c3 = sqrt(c2)
    let c3_re_bn = BigUint::from_str("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap();
    let c3_im_bn = BigUint::from_str("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap();
    let c3_re_fq: Fq = bn_to_field(&c3_re_bn);
    let c3_im_fq: Fq = bn_to_field(&c3_im_bn);
    let c3_fq2 = (c3_re_fq, c3_im_fq);
    let c3: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(c3_fq2);

    // c4
    let c4_re_bn = BigUint::from_str("2986490549723537757531757123281566653444223667895392953352176962020404273700864902437674267158202344424300571823643").unwrap();
    let c4_im_bn = BigUint::from_str("2758177894066318909194361808224047808735344068952776325476298594220885430911766052020476810444659821590302988943606").unwrap();
    let c4_re_fq: Fq = bn_to_field(&c4_re_bn);
    let c4_im_fq: Fq = bn_to_field(&c4_im_bn);
    let c4_fq2 = (c4_re_fq, c4_im_fq);
    let c4: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(c4_fq2);

    let c5_re_bn = BigUint::from_str("2364656849202240506627992632442075854991333434964021261821139393069706628902643788776727457290883891810009113172714").unwrap();
    let c5_im_bn = BigUint::from_str("1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679").unwrap();
    let c5_re_fq: Fq = bn_to_field(&c5_re_bn);
    let c5_im_fq: Fq = bn_to_field(&c5_im_bn);
    let c5_fq2 = (c5_re_fq, c5_im_fq);
    let c5: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_constant(c5_fq2);

    let zero: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_zero();
    let one: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_one();

    let mut tv1: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&u);
    let mut tv3: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&z, &tv1);
    let mut tv5: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&tv3);
    let mut xd:  AssignedFq2<Fq, Fr> = gseccc.fq2_add(&tv5, &tv3);
    let mut x1n: AssignedFq2<Fq, Fr> = gseccc.fq2_add(&xd, &one);
    x1n = gseccc.fq2_mul(&x1n, &b_prime);
    let minus_a_prime: AssignedFq2<Fq, Fr> = gseccc.fq2_neg(&a_prime);
    xd = gseccc.fq2_mul(&minus_a_prime, &xd);
    let e1: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &xd, &zero);
    let z_times_a_prime: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&z, &a_prime);
    xd = cmov(gseccc, &xd, &z_times_a_prime, &e1);
    let mut tv2: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&xd); // 11
    let mut gxd: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&tv2, &xd);
    tv2 = gseccc.fq2_mul(&a_prime, &tv2);
    let mut gx1: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&x1n);
    gx1 = gseccc.fq2_add(&gx1, &tv2);
    gx1 = gseccc.fq2_mul(&gx1, &x1n);
    tv2 = gseccc.fq2_mul(&b_prime, &gxd); // 16
    gx1 = gseccc.fq2_add(&gx1, &tv2);
    let mut tv4: AssignedFq2<Fq, Fr> = gseccc.fq2_square(&gxd);
    tv2 = gseccc.fq2_mul(&tv4, &gxd);
    tv4 = gseccc.fq2_square(&tv4); // 20
    tv2 = gseccc.fq2_mul(&tv2, &tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gx1);
    tv4 = gseccc.fq2_square(&tv4);
    tv4 = gseccc.fq2_mul(&tv2, &tv4); // 24

    // y = tv4^c1
    // Using the square-and-multiply algorithm with the constant c1.
    // First, initialize y to 1.  This initialization is independent
    // of prover input, so we can use the fq2_assign_one() method.
    let mut y: AssignedFq2<Fq, Fr> = gseccc.fq2_assign_one();
    for bit_char in c1_str.chars() {
        if bit_char == '0' {
            // If the current bit of c1 (big-endian) is 0, square y.
            y = gseccc.fq2_square(&y);
        } else {
            // If the current bit of c1 (big-endian) is 1, square y and multiply by tv4.
            y = gseccc.fq2_square(&y);
            y = gseccc.fq2_mul(&y, &tv4);
        }
    }
    y = gseccc.fq2_mul(&y, &tv2);
    tv4 = gseccc.fq2_mul(&y, &c2);
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd); // 29
    let e2: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx1);
    y = cmov(gseccc, &y, &tv4, &e2);
    tv4 = gseccc.fq2_mul(&y, &c3);
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd); // 34
    let e3: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx1);
    y = cmov(gseccc, &y, &tv4, &e3);
    tv4 = gseccc.fq2_mul(&tv4, &c2);
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd); // 39
    let e4: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx1);
    y = cmov(gseccc, &y, &tv4, &e4);
    let mut gx2: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&gx1, &tv5); // 42
    gx2 = gseccc.fq2_mul(&gx2, &tv3);
    tv5 = gseccc.fq2_mul(&y, &tv1);
    tv5 = gseccc.fq2_mul(&tv5, &u);
    tv1 = gseccc.fq2_mul(&tv5, &c4);
    tv4 = gseccc.fq2_mul(&tv1, &c2); // 47
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd);
    let e5: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx2);
    tv1 = cmov(gseccc, &tv1, &tv4, &e5);
    tv4 = gseccc.fq2_mul(&tv5, &c5); // 52
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd);
    let e6: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx2);
    tv1 = cmov(gseccc, &tv1, &tv4, &e6);
    tv4 = gseccc.fq2_mul(&tv4, &c2);
    tv2 = gseccc.fq2_square(&tv4);
    tv2 = gseccc.fq2_mul(&tv2, &gxd); // 59
    let e7: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx2);
    tv1 = cmov(gseccc, &tv1, &tv4, &e7);
    tv2 = gseccc.fq2_square(&y);
    tv2 = gseccc.fq2_mul(&tv2, &gxd); // 63
    let e8: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(gseccc, &tv2, &gx1);
    y = cmov(gseccc, &tv1, &y, &e8);
    tv2 = gseccc.fq2_mul(&tv3, &x1n);
    let mut xn: AssignedFq2<Fq, Fr> = cmov(gseccc, &tv2, &x1n, &e8);
    // For testing purposes only: replace with constrained sgn0 in the final version
    if sgn0_unconstrained(gseccc, &u) != sgn0_unconstrained(gseccc, &y) {
        y = gseccc.fq2_neg(&y);
    }
    // The straight-line program guarantees that xd is nonzero.
    let xd_inverse: AssignedFq2<Fq, Fr> = gseccc.fq2_unsafe_invert(&xd);
    let x: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&xn, &xd_inverse);

    // let xn_field_re = gseccc.base_integer_ctx.get_w(&xn.0);
    // let xn_field_im = gseccc.base_integer_ctx.get_w(&xn.1);
    // println!("xn = \n {:?} \n + I * {:?} \n", xn_field_re, xn_field_im);

    // let xd_field_re = gseccc.base_integer_ctx.get_w(&xd.0);
    // let xd_field_im = gseccc.base_integer_ctx.get_w(&xd.1);
    // println!("xd = \n {:?} \n + I * {:?} \n", xd_field_re, xd_field_im);

    // let y_field_re = gseccc.base_integer_ctx.get_w(&y.0);
    // let y_field_im = gseccc.base_integer_ctx.get_w(&y.1);
    // println!("y = \n {:?} \n + I * {:?} \n", y_field_re, y_field_im);

    (x, y)   
}

fn isogeny_map_in_context(
    gseccc: &mut GeneralScalarEccContext::<G1Affine, Fr>,
    x_prime: &AssignedFq2::<Fq, Fr>,
    y_prime: &AssignedFq2::<Fq, Fr>,
) -> (AssignedFq2<Fq, Fr>, AssignedFq2<Fq, Fr>) {
    let k_1_0_re_bn = BigUint::from_str("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542").unwrap();
    let k_1_0_im_bn = BigUint::from_str("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542").unwrap();
    let k_1_0_re: Fq = bn_to_field(&k_1_0_re_bn);
    let k_1_0_im: Fq = bn_to_field(&k_1_0_im_bn);
    let k_1_0 = gseccc.fq2_assign_constant((k_1_0_re, k_1_0_im));

    let k_1_1_re = Fq::zero();
    let k_1_1_im_bn = BigUint::from_str("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522").unwrap();
    let k_1_1_im: Fq = bn_to_field(&k_1_1_im_bn);
    let k_1_1 = gseccc.fq2_assign_constant((k_1_1_re, k_1_1_im));
    
    let k_1_2_re_bn = BigUint::from_str("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526").unwrap();
    let k_1_2_im_bn = BigUint::from_str("1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261").unwrap();
    let k_1_2_re: Fq = bn_to_field(&k_1_2_re_bn);
    let k_1_2_im: Fq = bn_to_field(&k_1_2_im_bn);
    let k_1_2 = gseccc.fq2_assign_constant((k_1_2_re, k_1_2_im));
    

    let k_1_3_re_bn = BigUint::from_str("3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033").unwrap();
    let k_1_3_re: Fq = bn_to_field(&k_1_3_re_bn);
    let k_1_3_im = Fq::zero();
    let k_1_3 = gseccc.fq2_assign_constant((k_1_3_re, k_1_3_im));
    

    // Constants used to compute x_den:
    let k_2_0_re = Fq::zero();
    let k_2_0_im_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715").unwrap();
    let k_2_0_im: Fq = bn_to_field(&k_2_0_im_bn);
    let k_2_0 = gseccc.fq2_assign_constant((k_2_0_re, k_2_0_im));

    let k_2_1_re_bn = BigUint::from_str("12").unwrap();
    let k_2_1_re: Fq = bn_to_field(&k_2_1_re_bn);
    let k_2_1_im_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775").unwrap();
    let k_2_1_im: Fq = bn_to_field(&k_2_1_im_bn);
    let k_2_1 = gseccc.fq2_assign_constant((k_2_1_re, k_2_1_im));

    // Constants used to compute y_num:
    let k_3_0_re_bn = BigUint::from_str("3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558").unwrap();
    let k_3_0_re: Fq = bn_to_field(&k_3_0_re_bn);
    let k_3_0_im_bn = BigUint::from_str("3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558").unwrap();
    let k_3_0_im: Fq = bn_to_field(&k_3_0_im_bn);
    let k_3_0 = gseccc.fq2_assign_constant((k_3_0_re, k_3_0_im));
    
    let k_3_1_re = Fq::zero();
    let k_3_1_im_bn = BigUint::from_str("889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518").unwrap();
    let k_3_1_im: Fq = bn_to_field(&k_3_1_im_bn);
    let k_3_1 = gseccc.fq2_assign_constant((k_3_1_re, k_3_1_im));

    let k_3_2_re_bn = BigUint::from_str("2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524").unwrap();
    let k_3_2_re: Fq = bn_to_field(&k_3_2_re_bn);
    let k_3_2_im_bn = BigUint::from_str("1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263").unwrap();
    let k_3_2_im: Fq = bn_to_field(&k_3_2_im_bn);
    let k_3_2 = gseccc.fq2_assign_constant((k_3_2_re, k_3_2_im));

    let k_3_3_re_bn = BigUint::from_str("2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776").unwrap();
    let k_3_3_re: Fq = bn_to_field(&k_3_3_re_bn);
    let k_3_3_im = Fq::zero();
    let k_3_3 = gseccc.fq2_assign_constant((k_3_3_re, k_3_3_im));

    // Constants used to compute y_den:
    let k_4_0_re_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355").unwrap();
    let k_4_0_re: Fq = bn_to_field(&k_4_0_re_bn);
    let k_4_0_im_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355").unwrap();
    let k_4_0_im: Fq = bn_to_field(&k_4_0_im_bn);
    let k_4_0 = gseccc.fq2_assign_constant((k_4_0_re, k_4_0_im));

    let k_4_1_re = Fq::zero();
    let k_4_1_im_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571").unwrap();
    let k_4_1_im: Fq = bn_to_field(&k_4_1_im_bn);
    let k_4_1 = gseccc.fq2_assign_constant((k_4_1_re, k_4_1_im));

    let k_4_2_re_bn = BigUint::from_str("18").unwrap();
    let k_4_2_re: Fq = bn_to_field(&k_4_2_re_bn);
    let k_4_2_im_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769").unwrap();
    let k_4_2_im: Fq = bn_to_field(&k_4_2_im_bn);
    let k_4_2 = gseccc.fq2_assign_constant((k_4_2_re, k_4_2_im));

    // For testing: in final version we should be able to do this with an
    // arbitrary AssignedFq2 input.
    let x_prime_re_bn = BigUint::from_str("3942339120143403995959884458065911863622623490130179671696530864527894030375709350085997343451924840375271949093332").unwrap();
    let x_prime_im_bn = BigUint::from_str("3523381697296058645143708860912139218718520142948191822158638626523448297128525915027995335789050238781038107799201").unwrap();
    // let x_prime_re = bn_to_field(&x_prime_re_bn);
    // let x_prime_im = bn_to_field(&x_prime_im_bn);
    let x_prime: AssignedFq2<Fq, Fr> = (
        gseccc.base_integer_ctx.assign_w(&x_prime_re_bn),
        gseccc.base_integer_ctx.assign_w(&x_prime_im_bn),
    );

    let y_prime_re_bn = BigUint::from_str("1842813153358560687634500333570189006426514559071004676715031705637331861897467026112259097700599015948196491964104").unwrap();
    let y_prime_im_bn = BigUint::from_str("1919560373509329990190398196596248904228486898136222165059580822353869402983639316101175960854421770934878934628156").unwrap();
    // let y_prime_re = bn_to_field(&y_prime_re_bn);
    // let y_prime_im = bn_to_field(&y_prime_im_bn);
    let y_prime: AssignedFq2<Fq, Fr> = (
        gseccc.base_integer_ctx.assign_w(&y_prime_re_bn),
        gseccc.base_integer_ctx.assign_w(&y_prime_im_bn),
    );

    let x_prime_squared = gseccc.fq2_square(&x_prime);
    let x_prime_cubed = gseccc.fq2_mul(&x_prime_squared, &x_prime);

    // Calculates x_num
    let x_num_constant_term = k_1_0;
    let x_num_degree_one_term = gseccc.fq2_mul(&k_1_1, &x_prime);
    let x_num_degree_two_term = gseccc.fq2_mul(&k_1_2, &x_prime_squared);
    let x_num_degree_three_term = gseccc.fq2_mul(&k_1_3, &x_prime_cubed);

    let mut x_num = gseccc.fq2_assign_zero();
    x_num = gseccc.fq2_add(&x_num, &x_num_constant_term);
    x_num = gseccc.fq2_add(&x_num, &x_num_degree_one_term);
    x_num = gseccc.fq2_add(&x_num, &x_num_degree_two_term);
    x_num = gseccc.fq2_add(&x_num, &x_num_degree_three_term);

    // Calculates x_den
    let x_den_constant_term = k_2_0;
    let x_den_degree_one_term = gseccc.fq2_mul(&k_2_1, &x_prime);
    let x_den_degree_two_term = x_prime_squared.clone(); // TODO: Constrain this!

    let mut x_den = gseccc.fq2_assign_zero();
    x_den = gseccc.fq2_add(&x_den, &x_den_constant_term);
    x_den = gseccc.fq2_add(&x_den, &x_den_degree_one_term);
    x_den = gseccc.fq2_add(&x_den, &x_den_degree_two_term);

    // Calculates y_num
    let y_num_constant_term = k_3_0;
    let y_num_degree_one_term = gseccc.fq2_mul(&k_3_1, &x_prime);
    let y_num_degree_two_term = gseccc.fq2_mul(&k_3_2, &x_prime_squared);
    let y_num_degree_three_term = gseccc.fq2_mul(&k_3_3, &x_prime_cubed);

    let mut y_num = gseccc.fq2_assign_zero();
    y_num = gseccc.fq2_add(&y_num, &y_num_constant_term);
    y_num = gseccc.fq2_add(&y_num, &y_num_degree_one_term);
    y_num = gseccc.fq2_add(&y_num, &y_num_degree_two_term);
    y_num = gseccc.fq2_add(&y_num, &y_num_degree_three_term);

    // Calculates y_den
    let y_den_constant_term = k_4_0;
    let y_den_degree_one_term = gseccc.fq2_mul(&k_4_1, &x_prime);
    let y_den_degree_two_term = gseccc.fq2_mul(&k_4_2, &x_prime_squared);
    let y_den_degree_three_term = x_prime_cubed;

    let mut y_den = gseccc.fq2_assign_zero();
    y_den = gseccc.fq2_add(&y_den, &y_den_constant_term);
    y_den = gseccc.fq2_add(&y_den, &y_den_degree_one_term);
    y_den = gseccc.fq2_add(&y_den, &y_den_degree_two_term);
    y_den = gseccc.fq2_add(&y_den, &y_den_degree_three_term);

    // Calculates x
    let x_den_inverse = gseccc.fq2_unsafe_invert(&x_den);
    let x = gseccc.fq2_mul(&x_num, &x_den_inverse);
    let x_re = gseccc.base_integer_ctx.get_w(&x.0);
    let x_im = gseccc.base_integer_ctx.get_w(&x.1);
    println!("x = {:?} \n + I * {:?}", x_re, x_im);

    // Calculates y
    let y_den_inverse = gseccc.fq2_unsafe_invert(&y_den);
    let y_num_over_y_den = gseccc.fq2_mul(&y_num, &y_den_inverse);
    let y = gseccc.fq2_mul(&y_prime, &y_num_over_y_den);
    let y_re = gseccc.base_integer_ctx.get_w(&y.0);
    let y_im = gseccc.base_integer_ctx.get_w(&y.1);
    println!("y = {:?} \n + I * {:?}", y_re, y_im);

    (x, y)
}

#[test]
fn simplified_swu_outputs_correct_test_vectors() {
    let mut gseccc = GeneralScalarEccContext::<G1Affine, Fr>::new(
        Rc::new(
            RefCell::new(
                Context::new()
            )
        )
    );

    // From the reference document's test vectors.
    // u[0] = 0x03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8 + I * 0x05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a
    // Hexadecimal values were converted using Boxentriq's online hex-to-decimal converter
    // so that the BigUint string parser can convert them to a BigUint.
    let u_re_bn = BigUint::from_str("593868448310005448561172252387029516360409945786457439875974315031640021389835649561235021338510064922970633805048").unwrap();
    let u_im_bn = BigUint::from_str("867375309489067512797459860887365951877054038763818448057326190302701649888849997836339069389536967202878289851290").unwrap();
    let u: AssignedFq2<Fq, Fr> = (
        gseccc.base_integer_ctx.assign_w(&u_re_bn),
        gseccc.base_integer_ctx.assign_w(&u_im_bn),
    );

    let (x, y) = simplified_swu_in_context(&mut gseccc, &u);

    let should_be_x_re_bn = BigUint::from_str("3942339120143403995959884458065911863622623490130179671696530864527894030375709350085997343451924840375271949093332").unwrap();
    let should_be_x_im_bn = BigUint::from_str("3523381697296058645143708860912139218718520142948191822158638626523448297128525915027995335789050238781038107799201").unwrap();
    let should_be_y_re_bn = BigUint::from_str("1842813153358560687634500333570189006426514559071004676715031705637331861897467026112259097700599015948196491964104").unwrap();
    let should_be_y_im_bn = BigUint::from_str("1919560373509329990190398196596248904228486898136222165059580822353869402983639316101175960854421770934878934628156").unwrap();

    let should_be_x_re_fq: Fq = bn_to_field(&should_be_x_re_bn);
    let should_be_x_im_fq: Fq = bn_to_field(&should_be_x_im_bn);
    let should_be_y_re_fq: Fq = bn_to_field(&should_be_y_re_bn);
    let should_be_y_im_fq: Fq = bn_to_field(&should_be_y_im_bn);

    let x_re_fq = gseccc.base_integer_ctx.get_w(&x.0);
    let x_im_fq = gseccc.base_integer_ctx.get_w(&x.1);
    let y_re_fq = gseccc.base_integer_ctx.get_w(&y.0);
    let y_im_fq = gseccc.base_integer_ctx.get_w(&y.1);

    assert_eq!(should_be_x_re_fq, x_re_fq);
    assert_eq!(should_be_x_im_fq, x_im_fq);
    assert_eq!(should_be_y_re_fq, y_re_fq);
    assert_eq!(should_be_y_im_fq, y_im_fq);
}