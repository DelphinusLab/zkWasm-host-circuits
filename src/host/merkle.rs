use std::error::Error;
use std::fmt;
use std::fmt::Debug;

/*
const LEAF_SIG: u8 = 0u8;
const INTERNAL_SIG: u8 = 1u8;
*/


#[derive(Debug)]
pub struct MerkleError {
    source: String,
    index: u32,
}

impl MerkleError {
    fn new(source: String, index: u32) -> Self {
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

pub trait MerkleLeaf<H: Debug+Clone> {
    fn hash(&self) -> H;
    fn index(&self) -> u32;
}

#[derive(Debug)]
pub struct MerkleProof<H: Debug+Clone, const D: usize> {
    pub source:H,
    pub root:H, // last is root
    pub assist:[H; D],
    pub index: u32,
}


pub trait MerkleTree<H:Debug+Clone, const D: usize> {
    type Leaf: MerkleLeaf<H>;
    type Id;
    fn construct(id: Self::Id) -> Self;
    fn hash(&self, a:H, b:H) -> H;
    fn boundary_check(&self, index: u32) -> Result<(), MerkleError> {
        if index as u32 >= (2_u32.pow(D as u32 + 1) - 1) {
            Err(MerkleError::new("path out of boundary".to_string(), index))
        } else {
            Ok(())
        }
    }
    fn leaf_check(&self, index: u32) -> Result<(), MerkleError> {
        if index as u32 >= (2_u32.pow(D as u32 -1) - 1) {
            Ok(())
        } else {
            Err(MerkleError::new("leaf path out of boundary".to_string(), index))
        }
    }

    fn get_hash(&self, index: u32) -> Result<H, MerkleError>;
    fn set_hash(&mut self, index: u32, hash: &H) -> Result<(), MerkleError>;
    fn set_leaf(&mut self, leaf: &Self::Leaf) -> Result<(), MerkleError>;
    fn get_leaf(&self, index: u32) -> Result<Self::Leaf, MerkleError>;
    fn get_sibling_index(&self, index: u32) -> u32 {
        if index % 2 == 1 {
            index+1
        } else {
            index-1
        }
    }
    fn get_proof_path(&self, index: u32) -> Result<[u32; D], MerkleError> {
        self.leaf_check(index)?;
        let mut p = index;
        let mut path = vec![];
        for _ in 0..D {
            let sibling = self.get_sibling_index(p);
            path.push(sibling);
            p = (p-1)/2;
        };
        Ok(path.try_into().unwrap())
    }
    fn get_leaf_with_proof(&self, index: u32) -> Result<(Self::Leaf, MerkleProof<H, D>), MerkleError> {
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
    fn set_leaf_with_proof(&mut self, leaf: &Self::Leaf) -> Result<MerkleProof<H, D>, MerkleError> {
        let index = leaf.index();
        let mut hash = leaf.hash();
        let (_, mut proof) = self.get_leaf_with_proof(index)?;
        proof.source = hash.clone();
        let mut p = index;
        self.set_leaf(leaf)?;
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

#[cfg(test)]
mod tests {
    use crate::host::merkle::{MerkleLeaf, MerkleTree, MerkleError};
    struct MerkleAsArray {
        id: String,
        data: [u64; 127] // 2^7-1 and depth = 6
    }
    struct MerkleU64Leaf {
        pub value: u64,
        pub index: u32,
    }

    impl MerkleLeaf<u64> for MerkleU64Leaf {
        fn index(&self) -> u32 { self.index }
        fn hash(&self) -> u64 { self.value }
    }

    impl MerkleTree<u64, 6> for MerkleAsArray {
        type Id = String;
        type Leaf = MerkleU64Leaf;
        fn construct(id: Self::Id) -> Self {
            MerkleAsArray {
                id,
                data: [0 as u64; 127]
            }
        }
        fn hash(&self, a:u64, b:u64) -> u64 {
            a + b 
        }
        fn get_hash(&self, index: u32) -> Result<u64, MerkleError> {
            self.boundary_check(index)?;
            Ok(self.data[index as usize])
        }
        fn set_hash(&mut self, index: u32, hash: &u64) -> Result<(), MerkleError> {
            self.boundary_check(index)?;
            self.data[index as usize] = *hash;
            Ok(())
        }
        fn set_leaf(&mut self, leaf: &Self::Leaf) -> Result<(), MerkleError> {
            self.leaf_check(leaf.index())?;
            self.data[leaf.index() as usize] = leaf.value;
            Ok(())
        }
        fn get_leaf(&self, index: u32) -> Result<Self::Leaf, MerkleError> {
            self.leaf_check(index)?;
            Ok(MerkleU64Leaf {
                value: self.data[index as usize],
                index
            })
        }
    }

    /* a
     * b c
     * - e f
     * - - g h
     *
     * sibling of g = h, e, b
     */

    #[test]
    fn test_merkle_path() {
       let mut mt = MerkleAsArray::construct("test".to_string());
       let mut leaf = mt.get_leaf(2_u32.pow(6) - 1).unwrap();
       leaf.value = 1;
       let proof = mt.set_leaf_with_proof(&leaf).unwrap();

       /* one update of 1 is 1 */
       let root = mt.get_hash(0).unwrap();
       assert_eq!(root, 1 as u64);

       let mut leaf = mt.get_leaf(2_u32.pow(6) + 2).unwrap();
       leaf.value = 2;
       let _proof = mt.set_leaf_with_proof(&leaf).unwrap();

       /* two leaves hash needs to be 3 */
       let root = mt.get_hash(0).unwrap();
       assert_eq!(root, 3 as u64);

       let mut leaf = mt.get_leaf(2_u32.pow(6) + 4).unwrap();
       leaf.value = 3;
       let _proof = mt.set_leaf_with_proof(&leaf).unwrap();
       /* two leaves hash needs to be 3 */
       let root = mt.get_hash(0).unwrap();
       assert_eq!(root, 6 as u64);

    }
}
