use crate::host::ExternalHostCallEntry;
use crate::host::ForeignInst;
use crate::utils::field_to_bn;
use halo2_proofs::arithmetic::BaseExt;
use num_bigint::BigUint;

pub mod bls381adaptor;
pub mod bn256adaptor;
pub mod hashadaptor;
pub mod merkleadaptor;
pub mod msmadaptor;

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
