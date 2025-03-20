use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::utils::field_to_bn;
use halo2_proofs::arithmetic::{BaseExt, FieldExt};
use num_bigint::BigUint;

// pub mod bls381adaptor;
pub mod bn256adaptor;
pub mod hashadaptor;
pub mod keccakadaptor;
pub mod merkleadaptor;
pub mod msmadaptor;

pub fn get_max_round(k: usize, reference_max: usize) -> usize {
    if k >= 22 {
        reference_max << (k - 22)
    } else {
        // we do not support host when k < 22
        0
    }
}

pub fn fr_to_args<F: BaseExt>(
    f: F,
    nblimbs: usize,
    sz: usize,
    op: ForeignInst,
) -> Vec<ExternalHostCallEntry> {
    let mut bn = field_to_bn(&f);
    let mut ret = vec![];
    for _ in 0..nblimbs {
        let d: BigUint = BigUint::from(1u128 << sz);
        let r = bn.clone() % d.clone();
        let value = if r == BigUint::from(0 as u32) {
            0 as u64
        } else {
            r.to_u64_digits()[0]
        };
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

pub fn get_selected_entries<Fr: FieldExt>(
    shared_operands: &Vec<Fr>,
    shared_opcodes: &Vec<Fr>,
    opcodes: &Vec<Fr>,
) -> Vec<((Fr, Fr), Fr)> {
    let entries = shared_operands
        .clone()
        .into_iter()
        .zip(shared_opcodes.clone());

    let v = entries
        .filter(|(_operand, opcode)| opcodes.contains(opcode))
        .collect::<Vec<(Fr, Fr)>>();

    let len = v.len();

    let shared_index: Vec<Fr> = v
        .iter()
        .enumerate()
        .map(|(i, _)| Fr::from((len - i) as u64))
        .collect();

    v.into_iter()
        .zip(shared_index)
        .collect::<Vec<((Fr, Fr), Fr)>>()
}
