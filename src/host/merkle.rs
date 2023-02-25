use std::error::Error;
use std::fmt;
use std::ops::ShrAssign;

#[derive(Debug)]
pub struct MerkleError {
    source: String,
    index: usize,
}

impl MerkleError {
    fn new(source: String, index: usize) -> Self {
        MerkleError {source, index}
    }
}

impl fmt::Display for MerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MerkleError {:?} {:?}", self.source, self.index)
    }
}

impl Error for MerkleError {
}

const LEAF_SIG: u8 = 0u8;
const INTERNAL_SIG: u8 = 1u8;

trait MerkleLeaf<H> {
    fn hash(&self, hash: &mut H) -> ();
    fn index(&self) -> usize;
    fn next(&self) -> usize;
}

struct Proof<H, const D: usize> {
    pub source:H,
    pub assist:[H; D], // last is root
    pub index: usize,
}


pub trait MerkleTree<H, const D: usize> {
    type Leaf: MerkleLeaf<H>;
    type Id;
    fn construct(id: Self::Id) -> Self;
    fn get_hash(&self, index: usize) -> Result<H, MerkleError>;
    fn set_hash(&self, index: usize) -> Result<H, MerkleError>;
    fn update_leaf(&self, leaf: &Self::Leaf) -> Result<Proof<H, D>, MerkleError>;
    fn get_leaf(&self, index: usize) -> Result<(Self::Leaf, Proof<H, D>), MerkleError>;
    fn get_path(&self, index: usize) -> Result<[usize; D], MerkleError> {
        if index as u32 > (2_u32.pow(D as u32) - 1) {
            Err(MerkleError::new("path out of boundary".to_string(), index))
        } else {
            let mut p = if index % 2 == 1 { index } else { index+1 };
            let mut path = vec![index];
            for i in 0..D-1 {
                path.push(p-1);
                p.shr_assign(1);
            };
            Ok(path.try_into().unwrap())
        }
    }
}
