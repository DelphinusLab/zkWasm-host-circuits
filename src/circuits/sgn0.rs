#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused)]

use halo2ecc_s::assign::{AssignedFq, AssignedFq2};
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::circuit::fq12::Fq2ChipOps;
use halo2ecc_s::circuit::general_scalar_ecc_chip;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::context::*;
use halo2ecc_s::utils::*;
use halo2_proofs::pairing::bls12_381::{G1Affine, Fq};
use halo2_proofs::pairing::bn256::{Fr, G1};
use num_bigint::BigUint;
use ripemd::digest::typenum::NonZero;
use std::cell::RefCell;
use std::num::NonZeroI128;
use std::rc::Rc;
use std::str::FromStr;

/// Constrains the output to be the dot product (in the base field) of
/// two input vectors of assigned base field elements of the same length.
/// Panics if the input vectors are not the same length.
fn dot_product(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<AssignedFq<Fq, Fr>>,
    b: &Vec<AssignedFq<Fq, Fr>>
) -> AssignedFq<Fq, Fr> {
    assert_eq!(a.len(), b.len());

    let zero_bn = BigUint::from_str("0").unwrap();
    let mut a_dot_b = gseccc.base_integer_ctx.assign_w(&zero_bn);
    let mut ai_times_bi = gseccc.base_integer_ctx.assign_w(&zero_bn);
    for i in 0..a.len() {
        ai_times_bi = gseccc.base_integer_ctx.int_mul(&a[i], &b[i]);
        a_dot_b = gseccc.base_integer_ctx.int_add(&a_dot_b, &ai_times_bi);
    }

    a_dot_b
}

/// Constrains each assigned base field element in a vector a to be either 0 or 1.
fn constrain_bits(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<AssignedFq<Fq, Fr>>
) {
    let zero = gseccc.base_integer_ctx.assign_int_constant(Fq::zero());
    let a_squared_componentwise: Vec<AssignedFq<Fq, Fr>> = a
        .into_iter()
        .map(|a_i| {
            gseccc.base_integer_ctx.int_square(&a_i)
        })
        .collect();
    let mut should_be_zero_vector: Vec<AssignedFq<Fq, Fr>> = vec![];
    for i in 0..a.len() {
        should_be_zero_vector.push(
            gseccc.base_integer_ctx.int_sub(
                &a_squared_componentwise[i], 
                &a[i]
            )
        );
        gseccc.base_integer_ctx.assert_int_equal(
            &should_be_zero_vector[i], 
            &zero,
        );
    }
}

// Assumes the input vectors consist only of assigned field elements
// that are all either equal to zero or one.  This condition can be constrained
// independently in a prior step if needed.
fn lexicographical_bitwise_comparison(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a_bits: &Vec<AssignedFq<Fq, Fr>>,
    b_bits: &Vec<AssignedFq<Fq, Fr>>
) -> AssignedFq<Fq, Fr> {
    assert_eq!(a_bits.len(), b_bits.len());
    let difference: Vec<AssignedFq<Fq, Fr>> = a_bits
        .into_iter()
        .enumerate()
        .map(|(i, ai)| {
            gseccc.base_integer_ctx.int_sub(&ai, &b_bits[i])
        })
        .collect();
    
    // Assigns c_0 = b_0 - a_0 without constraining.
    let difference_0_fq = gseccc.base_integer_ctx.get_w(&difference[0]);
    let difference_0_bn = field_to_bn(&difference_0_fq);
    let difference_0 = gseccc.base_integer_ctx.assign_w(&difference_0_bn);

    // Constrains c_0 = b_0 - a_0
    gseccc.base_integer_ctx.assert_int_equal(&difference_0, &difference[0]);
    
    let mut c_vec: Vec<AssignedFq<Fq, Fr>> = vec![difference_0];

    let zero_bn = BigUint::from_str("0").unwrap();
    let one = gseccc.base_integer_ctx.assign_int_constant(Fq::one());
    let mut previous_squared: AssignedFq<Fq, Fr>;
    let mut one_minus_previous_squared: AssignedFq<Fq, Fr>;
    for i in 1..a_bits.len() {
        previous_squared = gseccc.base_integer_ctx.int_square(&c_vec[i-1]);
        one_minus_previous_squared = gseccc.base_integer_ctx.int_sub(&one, &previous_squared);
        c_vec.push(gseccc.base_integer_ctx.int_mul(
            &one_minus_previous_squared, 
            &difference[i])
        );
    }
    
    let c: AssignedFq<Fq, Fr> = c_vec[c_vec.len() - 1].clone();
    c
}

const P_BINARY_STR: &str = "110100000000100010001111010100011100101111111111001101001101001001011000110111010011110110110010000110100101110101100110101110110010001110111010010111000010011110011100001010001001010111111011001110011000011010010101000001111011010110000111101100010010000011110101010111111111111111110101100010101001111111111111111111011100111111110111111111111111111111111111111111010101010101011";

fn binary_str_to_assigned_bits(
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

// Small helper function to turn a BigUint into its big-endian bit decomposition
// expressed as a vector of BigUints.  Used in the assigning step of a bitwise
// decomposition.
fn bn_to_bits_bn_be(bn: &BigUint) -> Vec<BigUint> {
    let two_bn = BigUint::from_str("2").unwrap();
    
    let mut bits: Vec<BigUint> = vec![];
    let mut current_bn = bn.clone();
    let mut current_bit: BigUint;
    for i in 0..bn.bits() {
        current_bit = &current_bn % &two_bn;
        current_bn = (&current_bn - &current_bit) / &two_bn;
        bits.insert(0, current_bit);
    }

    bits
}

/// Decomposes an input assigned base field element x into a vector of assigned
/// base field elements, all of which are equal to 0 or 1.
/// Constrains that each assigned base field element is indeed a bit,
/// and that the given vector of assigned bits is indeed a bit decomposition of x.
/// In other words, the bits raised to the appropriate powers of 2 and summed
/// is constrained to be equal to x.
/// The decomposition is big-endian, because having a big-endian decomposition
/// makes the constraints for bitwise lexicographical comparison more natural.
fn decompose_into_bits_be(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x: &AssignedFq<Fq, Fr>,
    length: usize
) -> Vec<AssignedFq<Fq, Fr>> {
    // Assigns without constraining.
    let x_reduced = gseccc.base_integer_ctx.reduce(&x);
    let x_fq = gseccc.base_integer_ctx.get_w(&x_reduced);
    let x_bn = field_to_bn(&x_fq);

    let zero_bn = BigUint::from_str("0").unwrap();
    let one_bn = BigUint::from_str("1").unwrap();
    let two_bn = BigUint::from_str("2").unwrap();
    let powers_of_two_bn: Vec<BigUint> = (0..length)
        .map(|i| {
            two_bn.pow(i as u32)
        })
        .collect();
    let powers_of_two_fq: Vec<Fq> = powers_of_two_bn
        .into_iter()
        .map(|bn| {
            bn_to_field(&bn)
        })
        .collect();
    let powers_of_two: Vec<AssignedFq<Fq, Fr>> = powers_of_two_fq
        .into_iter()
        .map(|fq| {
            gseccc.base_integer_ctx.assign_int_constant(fq)
        })
        .collect();


    todo!()
}

fn mod2(
    gseccc: &mut GeneralScalarEccContext<G1Affine, Fr>,
    x_bits: &Vec<AssignedFq<Fq, Fr>>,
    x: &AssignedFq<Fq, Fr>
) -> AssignedFq<Fq, Fr> {
    let p_bits = binary_str_to_assigned_bits(gseccc, P_BINARY_STR);
    

    todo!()
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

    let zero_bn = BigUint::from_str("0").unwrap();
    let zero = gseccc.base_integer_ctx.assign_w(&zero_bn);
    // println!("zero = {:?}", zero);

    let one_bn = BigUint::from_str("1").unwrap();
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
fn test_bn_to_bits_bn_be() {
    
}