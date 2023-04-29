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

pub trait MerkleNode <H: Debug+Clone> {
    fn hash(&self) -> H;
    fn index(&self) -> u32;
    fn set(&mut self, data: &Vec<u8>);
}

#[derive(Debug)]
pub struct MerkleProof<H: Debug+Clone, const D: usize> {
    pub source:H,
    pub root:H, // last is root
    pub assist:[H; D],
    pub index: u32,
}


pub trait MerkleTree<H:Debug+Clone, const D: usize> {
    type Node: MerkleNode<H>;
    type Id;
    fn construct(id: Self::Id, root: H) -> Self;
    fn hash(a:&H, b:&H) -> H;
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

    fn get_node(&self, index: u32) -> Result<Self::Node, MerkleError>;
    fn set_parent_hash(&mut self, index: u32, hash: &H, left: &H, right: &H) -> Result<(), MerkleError>;
    fn set_leaf(&mut self, leaf: &Self::Node) -> Result<(), MerkleError>;
    fn get_leaf(&self, index: u32) -> Result<Self::Node, MerkleError> {
        self.leaf_check(index)?;
        self.get_node(index)
    }
    fn get_sibling_index(&self, index: u32) -> u32 {
        if index % 2 == 1 {
            index+1
        } else {
            index-1
        }
    }

    /* index from root to the leaf */
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

    fn get_leaf_with_proof(&self, index: u32) -> Result<(Self::Node, MerkleProof<H, D>), MerkleError> {
        let path = self.get_proof_path(index)?;
        let leaf = self.get_leaf(index)?;
        let assist:Vec<H> = path.into_iter()
                .map(|i| {
                    let node = self.get_node(i)?;
                    Ok(node.hash())
                })
                .collect::<Result<Vec<H>, _>>()?;
        Ok((leaf, MerkleProof {
            source: self.get_node(index)?.hash(),
            root: self.get_node(0)?.hash(),
            assist: assist.try_into().unwrap(),
            index
        }))
    }

    fn set_leaf_with_proof(&mut self, leaf: &Self::Node) -> Result<MerkleProof<H, D>, MerkleError> {
        let index = leaf.index();
        let mut hash = leaf.hash();
        let (_, mut proof) = self.get_leaf_with_proof(index)?;
        proof.source = hash.clone();
        let mut p = index;
        self.set_leaf(leaf)?;
        for i in 0..D {
            let old_hash = hash;
            let (left, right) = if p % 2 == 1 {
                (&old_hash, &proof.assist[i])
            } else {
                (&proof.assist[i], &old_hash)
            };
            hash = Self::hash(left, right);
            p = (p-1)/2;
            self.set_parent_hash(p, &hash, left, right)?;
        };
        proof.root = hash;
        Ok(proof)
    }

    fn update_leaf_data_with_proof(&mut self, index: u32, data: &Vec<u8>) -> Result<MerkleProof<H, D>, MerkleError> {
        let mut leaf = self.get_leaf(index)?;
        leaf.set(data);
        self.set_leaf_with_proof(&leaf)
    }
}

#[cfg(test)]
mod tests {
    use crate::host::merkle::{MerkleNode, MerkleTree, MerkleError};
    struct MerkleAsArray {
        data: [u64; 127] // 2^7-1 and depth = 6
    }

    struct MerkleU64Node {
        pub value: u64,
        pub index: u32,
    }

    impl MerkleNode<u64> for MerkleU64Node{
        fn index(&self) -> u32 { self.index }
        fn hash(&self) -> u64 { self.value }
        fn set(&mut self, value: &Vec<u8>) {
            let v:[u8; 8] = value.clone().try_into().unwrap();
            self.value = u64::from_le_bytes(v);
        }
    }

    impl MerkleTree<u64, 6> for MerkleAsArray {
        type Id = String;
        type Node = MerkleU64Node;
        fn construct(_id: Self::Id, _hash: u64) -> Self {
            MerkleAsArray {
                data: [0 as u64; 127]
            }
        }
        fn hash(a:&u64, b:&u64) -> u64 {
            a + b
        }
        fn get_node(&self, index: u32) -> Result<Self::Node, MerkleError> {
            self.boundary_check(index)?;
            Ok(MerkleU64Node {value: self.data[index as usize], index})
        }
        fn set_parent_hash(&mut self, index: u32, hash: &u64, _left: &u64, _right: &u64) -> Result<(), MerkleError> {
            self.boundary_check(index)?;
            self.data[index as usize] = *hash;
            Ok(())
        }
        fn set_leaf(&mut self, leaf: &Self::Node) -> Result<(), MerkleError> {
            self.leaf_check(leaf.index())?;
            self.data[leaf.index() as usize] = leaf.value;
            Ok(())
        }
        fn get_leaf(&self, index: u32) -> Result<Self::Node, MerkleError> {
            self.leaf_check(index)?;
            Ok(MerkleU64Node{
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
       let mut mt = MerkleAsArray::construct("test".to_string(), 0);
       let mut leaf = mt.get_leaf(2_u32.pow(6) - 1).unwrap();
       leaf.value = 1;
       let _proof = mt.set_leaf_with_proof(&leaf).unwrap();

       /* one update of 1 is 1 */
       let root = mt.get_node(0).unwrap();
       assert_eq!(root.hash(), 1 as u64);

       let mut leaf = mt.get_leaf(2_u32.pow(6) + 2).unwrap();
       leaf.value = 2;
       let _proof = mt.set_leaf_with_proof(&leaf).unwrap();

       /* two leaves hash needs to be 3 */
       let root = mt.get_node(0).unwrap();
       assert_eq!(root.hash(), 3 as u64);

       let mut leaf = mt.get_leaf(2_u32.pow(6) + 4).unwrap();
       leaf.value = 3;
       let _proof = mt.set_leaf_with_proof(&leaf).unwrap();
       /* two leaves hash needs to be 3 */
       let root = mt.get_node(0).unwrap();
       assert_eq!(root.hash(), 6 as u64);
    }
}
