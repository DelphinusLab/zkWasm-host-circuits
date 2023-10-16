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
use halo2_proofs::pairing::bn256::Fr;
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

fn simplified_swu_in_context(u_re_bn: &BigUint, u_im_bn: &BigUint) {
    let ctx = Rc::new(RefCell::new(Context::new()));
    let mut gseccc = GeneralScalarEccContext::<G1Affine, Fr>::new(ctx);

    let u: AssignedFq2<Fq, Fr> = (
        gseccc.base_integer_ctx.assign_w(u_re_bn),
        gseccc.base_integer_ctx.assign_w(u_im_bn)
    );

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
    let e1: AssignedFq2<Fq, Fr> = fq2_assign_equality_condition(&mut gseccc, &xd, &zero);
    let z_times_a_prime: AssignedFq2<Fq, Fr> = gseccc.fq2_mul(&z, &a_prime);
    xd = cmov(&mut gseccc, &xd, &z_times_a_prime, &e1);
    


}

#[test]
fn simplified_swu_outputs_correct_test_vectors() {
    // From the reference document's test vectors.
    // u[0] = 0x03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8 + I * 0x05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a
    // Hexadecimal values were converted using Boxentriq's online hex-to-decimal converter
    // so that the BigUint string parser can convert them to a BigUint.
    let u_re_bn = BigUint::from_str("593868448310005448561172252387029516360409945786457439875974315031640021389835649561235021338510064922970633805048").unwrap();
    let u_im_bn = BigUint::from_str("867375309489067512797459860887365951877054038763818448057326190302701649888849997836339069389536967202878289851290").unwrap();
}