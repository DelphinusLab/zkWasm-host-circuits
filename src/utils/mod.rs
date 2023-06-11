use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigUint;
use halo2_proofs::circuit::AssignedCell;

pub fn field_to_bn<F: BaseExt>(f: &F) -> BigUint {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    BigUint::from_bytes_le(&bytes[..])
}

pub fn bn_to_field<F: BaseExt>(bn: &BigUint) -> F {
    let mut bytes = bn.to_bytes_le();
    bytes.resize(48, 0);
    let mut bytes = &bytes[..];
    F::read(&mut bytes).unwrap()
}


pub fn field_to_u32<F: FieldExt>(f: &F) -> u32 {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    u32::from_le_bytes(bytes[0..4].try_into().unwrap())
}

pub fn field_to_u64<F: FieldExt>(f: &F) -> u64 {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    u64::from_le_bytes(bytes[0..8].try_into().unwrap())
}


pub fn u32_to_limbs<F: FieldExt>(v: u32) -> [F; 4] {
    let mut rem = v;
    let mut r = vec![];
    for _ in 0..4 {
        r.append(&mut vec![F::from((rem % 256) as u64)]);
        rem = rem/256;
    }
    r.try_into().unwrap()
}

pub fn cell_to_u32<F: FieldExt>(cell: &AssignedCell<F, F>) -> u32 {
    cell.value().map_or(0, |x| field_to_u32(x))
}

pub fn cell_to_limbs<F: FieldExt>(cell: &AssignedCell<F, F>) -> [F; 4] {
    let a = cell_to_u32(cell);
    u32_to_limbs(a)
}

pub struct GateCell {
    pub cell: [usize;3],
    pub name: String,
}

pub mod params;
pub mod macros;
