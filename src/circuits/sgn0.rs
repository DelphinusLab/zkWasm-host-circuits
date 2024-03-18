#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused)]

use halo2ecc_s::assign::{AssignedFq, AssignedFq2, AssignedInteger};
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::circuit::fq12::Fq2ChipOps;
use halo2ecc_s::circuit::general_scalar_ecc_chip;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::context::{Context, GeneralScalarEccContext};
use halo2ecc_s::utils::{field_to_bn, bn_to_field};
use halo2_proofs::pairing::bls12_381::{G1Affine, Fq};
use halo2_proofs::pairing::bn256::{Fr, G1};
use num_bigint::BigUint;
use ripemd::digest::typenum::NonZero;
use std::cell::RefCell;
use std::num::NonZeroI128;
use std::rc::Rc;
use std::str::FromStr;
use ark_std::{One, Zero};
use ff::Field;
use std::fmt::Debug;

/// Constrains the output to be the dot product (in the base field) of
/// two input vectors of assigned base field elements of the same length.
/// Panics if the input vectors are not the same length.
fn dot_product(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<AssignedFq<Fq, Fr>>,
    b: &Vec<AssignedFq<Fq, Fr>>
) -> AssignedFq<Fq, Fr> {
    assert_eq!(a.len(), b.len());

    a.iter().zip(b.iter())
        .fold(gseccc.base_integer_ctx.assign_int_constant(Fq::zero()), |acc, (ai, bi)| {
            let ai_times_bi = gseccc.base_integer_ctx.int_mul(ai, bi);
            gseccc.base_integer_ctx.int_add(&acc, &ai_times_bi)
        })
}

/// Constrains each assigned base field element in a vector a to be either 0 or 1.
fn constrain_bits(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<AssignedFq<Fq, Fr>>
) {
    println!("base before cons is {:?}", gseccc.base_integer_ctx.ctx.borrow_mut().base_offset);
    println!("range before cons is{:?}", gseccc.base_integer_ctx.ctx.borrow_mut().range_offset);

    let zero = gseccc.base_integer_ctx.assign_int_constant(Fq::zero());
    let one = gseccc.base_integer_ctx.assign_int_constant(Fq::one());

    for a_i in a.iter() {
        let ai_square = gseccc.base_integer_ctx.int_square(&a_i);
        let ai_square_minus_ai = gseccc.base_integer_ctx.int_sub(&ai_square, &a_i);
        gseccc.base_integer_ctx.assert_int_equal(&ai_square_minus_ai, &zero);
    }

    println!("base after cons is {:?}", gseccc.base_integer_ctx.ctx.borrow_mut().base_offset);
    println!("range after cons is{:?}", gseccc.base_integer_ctx.ctx.borrow_mut().range_offset);
}

/// Takes as input two vectors of assigned base field elements of equal length,
/// each of which has all entries equal to either 0 or 1.  *Assumes* that both
/// input vectors consist only of bits, but *panics* if they are not equal in
/// length. Thus the condition that each vector consists only of bits must be
/// constrained in a prior step.
///
/// Let a an b be the big-endian interpretation of `a_bits` and `b_bits`,
/// respectively, as integers.  This function returns an assigned base field
/// element that is equal to:
///     * 1 if a < b
///     * 0 if a = b
///     * -1 (= p-1) if a > b
fn lexicographical_comparison(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a_bits: &Vec<AssignedFq<Fq, Fr>>,
    b_bits: &Vec<AssignedFq<Fq, Fr>>,
) -> AssignedFq<Fq, Fr> {
    assert_eq!(a_bits.len(), b_bits.len());

    println!("base before lex is {:?}", gseccc.base_integer_ctx.ctx.borrow_mut().base_offset);
    println!("range before lex is{:?}", gseccc.base_integer_ctx.ctx.borrow_mut().range_offset);

    let zero = gseccc.base_integer_ctx.assign_int_constant(Fq::zero());
    let one = gseccc.base_integer_ctx.assign_int_constant(Fq::one());
    let minus_one = gseccc.base_integer_ctx.int_sub(&zero, &one);

    let mut result = zero.clone();

    for (ai, bi) in a_bits.iter().zip(b_bits.iter()) {
        let diff = gseccc.base_integer_ctx.int_sub(bi, ai);
        let is_diff_zero = gseccc.base_integer_ctx.is_int_equal(&diff, &zero);
        let is_diff_one = gseccc.base_integer_ctx.is_int_equal(&diff, &one);

        if is_diff_zero.0.val == Fr::zero() {
            continue;
        } else { // diff != 0
            if is_diff_one.0.val == Fr::one() {
                result = one.clone();
                break;
            } else { // diff != 0 and diff != 1
                result = minus_one.clone();
                break;
            }
        }
    }

    result
}

const P_BINARY_STR: &str = "110100000000100010001111010100011100101111111111001101001101001001011000110111010011110110110010000110100101110101100110101110110010001110111010010111000010011110011100001010001001010111111011001110011000011010010101000001111011010110000111101100010010000011110101010111111111111111110101100010101001111111111111111111011100111111110111111111111111111111111111111111010101010101011";

fn binary_str_to_assigned_constant_bits(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    binary_str: &str
) -> Vec<AssignedFq<Fq, Fr>> {
    binary_str.chars()
        .map(|bit| {
            if (bit == '0') {
                gseccc.base_integer_ctx.assign_int_constant(Fq::zero())
            } else if (bit == '1') {
                gseccc.base_integer_ctx.assign_int_constant(Fq::one())
            } else {
                panic!()
            }
        })
        .collect()
}

// Small helper function to turn a BigUint into its big-endian bit decomposition,
// padded to a fixed length, expressed as a vector of BigUints.   Used in the
// assigning step of an in-circuit bitwise decomposition.  Panics if the length
// of the input BigUint in bits is greater than `length`.
fn bn_to_bits_bn_be_fixed_length(
    bn: &BigUint,
    length: usize
) -> Vec<BigUint> {
    assert!((bn.bits() as usize) <= length);

    let mut bn_bit = bn.to_radix_be(2);
    for i in (bn.bits() as usize)..length {
        bn_bit.insert(0, 0u8);
    }
    let result: Vec<BigUint> = bn_bit.into_iter().map(|x| BigUint::from(x as u64)).collect();

    result
}

/// Decomposes an input assigned base field element x into a vector of assigned
/// base field elements, all of which are equal to 0 or 1.
/// Constrains that each assigned base field element is indeed a bit,
/// and that the given vector of assigned bits is indeed a bit decomposition of x.
/// In other words, the bits raised to the appropriate powers of 2 and summed
/// is constrained to be equal to x.
/// The decomposition is big-endian, because having a big-endian decomposition
/// makes the constraints for bitwise lexicographical comparison more natural.
/// `length` must be passed in because we cannot alter the (fixed) behavior of
/// the circuit based on the (variable) value of x.  When we use this function
/// later, the value of `length` will be the length of p (the modulus of the
/// base field) in bits, which in our case is 381.
fn decompose_into_bits_be(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x: &AssignedFq<Fq, Fr>,
    length: usize
) -> Vec<AssignedFq<Fq, Fr>> {
    // Assigns without constraining.
    println!("base before dec is {:?}", gseccc.base_integer_ctx.ctx.borrow_mut().base_offset);
    println!("range before dec is{:?}", gseccc.base_integer_ctx.ctx.borrow_mut().range_offset);
    let x_reduced = gseccc.base_integer_ctx.reduce(&x);
    let x_fq = gseccc.base_integer_ctx.get_w(&x_reduced);
    let x_bn = field_to_bn(&x_fq);
    let x_bits_bn_be = bn_to_bits_bn_be_fixed_length(&x_bn, length);
    let x_bits_be: Vec<AssignedFq<Fq, Fr>> = x_bits_bn_be
        .into_iter()
        .map(|bit| {
            gseccc.base_integer_ctx.assign_w(&bit)
        })
        .collect();

    // Constrains each claimed bit (assigned base field element/AssignedFq)
    // in the given decomposition of x to be a bit (either 0 or 1).
    constrain_bits(gseccc, &x_bits_be);

    let mut acc = Fq::one();
    let one_fq = Fq::one();

    let mut powers_of_two_fq_be: Vec<Fq> = vec![one_fq];

    for _ in 1..length {
        powers_of_two_fq_be.push(acc.double());
        acc = acc.double();
    };

    powers_of_two_fq_be.reverse();

    let powers_of_two_be: Vec<AssignedFq<Fq, Fr>> = powers_of_two_fq_be
        .into_iter()
        .map(|fq| {
            gseccc.base_integer_ctx.assign_int_constant(fq)
        })
        .collect();

    let must_equal_x = dot_product(gseccc, &x_bits_be, &powers_of_two_be);
    gseccc.base_integer_ctx.assert_int_equal(&must_equal_x, &x);

    println!("base after dec is {:?}", gseccc.base_integer_ctx.ctx.borrow_mut().base_offset);
    println!("range after dec is{:?}", gseccc.base_integer_ctx.ctx.borrow_mut().range_offset);

    x_bits_be
}

fn mod2(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x: &AssignedFq<Fq, Fr>
) -> AssignedFq<Fq, Fr> {
    let p_bits = binary_str_to_assigned_constant_bits(gseccc, P_BINARY_STR);
    let x_bits_be = decompose_into_bits_be(gseccc, x, P_BINARY_STR.len());
    let y = lexicographical_comparison(gseccc, &x_bits_be, &p_bits);

    let one = gseccc.base_integer_ctx.assign_int_constant(Fq::one());
    let two = gseccc.base_integer_ctx.assign_int_constant(Fq::one().double());

    let aux1 = gseccc.base_integer_ctx.int_mul(&two, &x_bits_be[x_bits_be.len() - 1]);
    let aux2 = gseccc.base_integer_ctx.int_sub(&y, &one);
    let aux3 = gseccc.base_integer_ctx.int_add(&aux1, &aux2);
    let (_, aux4) = gseccc.base_integer_ctx.int_div(&y, &two);
    let s = gseccc.base_integer_ctx.int_mul(&aux3, &aux4);

    s
}

pub fn sgn0(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x: &AssignedFq2<Fq, Fr>
) -> AssignedFq<Fq, Fr> {
    let x_re_fq = gseccc.base_integer_ctx.get_w(&x.0);
    let x_re_mod2 = mod2(gseccc, &x.0);
    let x_im_mod2 = mod2(gseccc, &x.1);

    let zero = gseccc.base_integer_ctx.assign_int_constant(Fq::zero());
    let one = gseccc.base_integer_ctx.assign_int_constant(Fq::one());

    // Assigns a new auxiliary variable z_prime, without constraining.
    // z_prime is not important except to constrain z.
    let z_prime_fq = if x_re_fq == Fq::zero() {
        Fq::zero()
    } else {
        x_re_fq.invert().unwrap()
    };
    let z_prime_bn = field_to_bn(&z_prime_fq);
    let z_prime = gseccc.base_integer_ctx.assign_w(&z_prime_bn);

    // This constrains a variable z to satisfy z =
    // * 1 if x = 0
    // * 0 otherwise.
    let aux1 = gseccc.base_integer_ctx.int_mul(&z_prime, &x.0); // z'x_re
    let z = gseccc.base_integer_ctx.int_sub(&one, &aux1); // 1 - z'x_re
    let aux2 = gseccc.base_integer_ctx.int_mul(&x.0, &z); // x_re(1 - z'x_re)
    gseccc.base_integer_ctx.assert_int_equal(&aux2, &zero); // x_re(1 - z'x_re) = 0

    let aux3 = gseccc.base_integer_ctx.int_mul(&z, &x_im_mod2); // z * x_im_mod2
    let aux4 = gseccc.base_integer_ctx.int_mul(&x_re_mod2, &aux3); // z * x_re_mod2 * x_im_mod2
    let aux5 = gseccc.base_integer_ctx.int_sub(&aux3, &aux4); // (z * x_im_mod2) - (z * x_re_mod2 * x_im_mod2)
    let sgn0 = gseccc.base_integer_ctx.int_add(&x_re_mod2, &aux5); // sgn0 = x_re_mod2 + (z * x_im_mod2) - (z * x_re_mod2 * x_im_mod2)

    sgn0
}

fn pretty_print_assigned_fq(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x: &AssignedFq<Fq, Fr>,
) {
    let x_fq = gseccc.base_integer_ctx.get_w(x);
    println!("{:?}", x_fq);
}

#[test]
fn does_int_add_reduce_mod_p() {
    let mut gseccc = GeneralScalarEccContext::<G1Affine, Fr>::new(
        Rc::new(
            RefCell::new(
                Context::new()
            )
        )
    );

    let zero_bn = BigUint::from(0u64);
    let zero = gseccc.base_integer_ctx.assign_w(&zero_bn);
    // println!("zero = {:?}", zero);

    let one_bn = BigUint::from(1u64);
    let one = gseccc.base_integer_ctx.assign_w(&one_bn);
    // println!("one = {:?}", one);

    let p_minus_one_bn = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap();
    let p_minus_one = gseccc.base_integer_ctx.assign_w(&p_minus_one_bn);
    // println!("p_minus_one = {:?}", p_minus_one);

    let p = gseccc.base_integer_ctx.int_add(&p_minus_one, &one);
    // println!("p = {:?}", p);

    gseccc.base_integer_ctx.assert_int_equal(&p, &zero);
    println!("base_integer_ctx = {:?}", gseccc.base_integer_ctx);
}

#[test]
fn test_binary_str_to_assigned_constant_bits() {
    let mut gseccc =
        GeneralScalarEccContext::<G1Affine, Fr>::new(Rc::new(RefCell::new(Context::new())));
    let six_binary_str_be: &str = "110";
    let six_assigned_constant_bits_be =
        binary_str_to_assigned_constant_bits(&mut gseccc, six_binary_str_be);

    println!(
        "6 in assigned constant bits (big-endian) is {:?}",
        six_assigned_constant_bits_be
    );
}

#[test]
fn test_lexicographical_bitwise_comparison() {
    let mut gseccc =
        GeneralScalarEccContext::<G1Affine, Fr>::new(Rc::new(RefCell::new(Context::new())));

    // 4 decimal big-endian = 100 binary big-endian
    let four_bn = BigUint::from_str("4").unwrap();
    let four = gseccc.base_integer_ctx.assign_w(&four_bn);

    // 11 decimal big-endian = 1011 binary big-endian
    let eleven_bn = BigUint::from_str("11").unwrap();
    let eleven = gseccc.base_integer_ctx.assign_w(&eleven_bn);

    // 100 decimal big-endian = 1100100 binary big-endian
    let one_hundred_bn = BigUint::from_str("100").unwrap();
    let one_hundred = gseccc.base_integer_ctx.assign_w(&eleven_bn);

    // Longest number that we want to compare is 1100100 with a length of 7.
    let four_bits_be = decompose_into_bits_be(&mut gseccc, &four, 7);
    // println!("Four expressed as seven bits big-endian = ");
    // pretty_print_vec_assigned_fq(&mut gseccc, &four_bits_be);

    let eleven_bits_be = decompose_into_bits_be(&mut gseccc, &eleven, 7);

    let one_hundred_bits_be = decompose_into_bits_be(&mut gseccc, &one_hundred, 7);

    // 4 < 11 so should output 1
    let is_eleven_less_than_four =
        lexicographical_comparison(&mut gseccc, &eleven_bits_be, &four_bits_be);

    // Printed out 0, so there is an issue here.
    println!("Is 11 < 4?  Should be -1 = ");
    pretty_print_assigned_fq(&mut gseccc, &is_eleven_less_than_four);
}

#[test]
fn test_bn_to_bits_bn_be_fixed_length() {
    let nineteen_bn = BigUint::from_str("19").unwrap();
    let nineteen_bits_bn_be = bn_to_bits_bn_be_fixed_length(&nineteen_bn, 381);
    println!("As a 381-bit BigUint vector in big-endian binary, 19 = {:?}", nineteen_bits_bn_be);
    println!("Length = {:?}", nineteen_bits_bn_be.len());
}