use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigUint;
use halo2_proofs::circuit::AssignedCell;

#[derive(Clone, Debug)]
pub struct Limb<F: FieldExt> {
    pub cell: Option<AssignedCell<F, F>>,
    pub value: F
}

impl<F: FieldExt> Limb<F> {
    pub fn new(cell: Option<AssignedCell<F, F>>, value: F) -> Self {
        Limb { cell, value }
    }
    pub fn get_the_cell(&self) -> AssignedCell<F,F> {
        self.cell.as_ref().unwrap().clone()
    }
}

pub fn data_to_bytes<F:BaseExt>(fs: Vec<F>) -> Vec<u8> {
    let mut bytes = vec![];
    for f in fs.iter() {
        let mut b = vec![];
        f.write(&mut b).unwrap();
        b.resize(16, 0);
        bytes.append(&mut b);
    }
    bytes
}

pub fn field_to_bytes<F: BaseExt>(f: &F) -> [u8; 32] {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    bytes.try_into().unwrap()
}

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

pub fn bytes_to_field<F: BaseExt>(bytes: &[u8; 32]) -> F {
    F::read(&mut &bytes.clone().to_vec()[..]).unwrap()
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




#[derive (Debug)]
pub struct GateCell {
    pub cell: [usize;3],
    pub name: String,
}

pub mod params;
pub mod macros;
