use std::error::Error;
use std::fmt;
use std::fmt::Debug;

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

pub trait MerkleLeaf<H: Debug+Clone> {
    fn hash(&self) -> H;
    fn index(&self) -> usize;
    fn next(&self) -> usize;
}

pub struct MerkleProof<H: Debug+Clone, const D: usize> {
    pub source:H,
    pub root:H, // last is root
    pub assist:[H; D],
    pub index: usize,
}


pub trait MerkleTree<H:Debug+Clone, const D: usize> {
    type Leaf: MerkleLeaf<H>;
    type Id;
    fn construct(id: Self::Id) -> Self;
    fn hash(&self, a:H, b:H) -> H;
    fn get_hash(&self, index: usize) -> Result<H, MerkleError>;
    fn set_hash(&self, index: usize, hash: &H) -> Result<H, MerkleError>;
    fn get_leaf(&self, index: usize) -> Result<Self::Leaf, MerkleError>;
    fn get_sibling_index(&self, index: usize) -> usize {
        if index % 2 == 1 {
            index+1
        } else {
            index-1
        }
    }
    fn get_proof_path(&self, index: usize) -> Result<[usize; D], MerkleError> {
        if index as u32 > (2_u32.pow(D as u32) - 1) {
            Err(MerkleError::new("path out of boundary".to_string(), index))
        } else {
            let mut p = index;
            let mut path = vec![index];
            for _ in 0..D {
                let sibling = self.get_sibling_index(p);
                path.insert(0, sibling);
                p = (p-1)/2;
            };
            Ok(path.try_into().unwrap())
        }
    }
    fn get_leaf_with_proof(&self, index: usize) -> Result<(Self::Leaf, MerkleProof<H, D>), MerkleError> {
        let path = self.get_proof_path(index)?;
        let leaf = self.get_leaf(index)?;
        let assist:Vec<H> = path.into_iter()
                .map(|i| self.get_hash(i))
                .collect::<Result<Vec<H>, MerkleError>>()?;
        Ok((leaf, MerkleProof {
            source: self.get_hash(index)?,
            root: self.get_hash(0)?,
            assist: assist.try_into().unwrap(),
            index
        }))
    }
    fn set_leaf_with_proof(&self, leaf: &Self::Leaf) -> Result<MerkleProof<H, D>, MerkleError> {
        let index = leaf.index();
        let mut hash = leaf.hash();
        let (_, mut proof) = self.get_leaf_with_proof(index)?;
        proof.source = hash.clone();
        let mut p = index;
        self.set_hash(p, &hash)?;
        for i in 0..D {
            hash = if p % 2 == 1 {
                self.hash(hash.clone(), proof.assist[i].clone())
            } else {
                self.hash(proof.assist[i].clone(), hash)
            };
            p = (p-1)/2;
            self.set_hash(p, &hash)?;
        };
        proof.root = hash;
        Ok(proof)
    }
}
