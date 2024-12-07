use std::error::Error;
use std::fmt;
use std::fmt::Debug;

#[derive(Debug)]
pub enum MerkleErrorCode {
    InvalidLeafIndex,
    InvalidHash,
    InvalidDepth,
    InvalidIndex,
    RecordNotFound,
    UnexpectedDBError,
}

#[derive(Debug)]
pub struct MerkleError {
    source: [u8; 32],
    index: u64,
    code: MerkleErrorCode,
}

impl MerkleError {
    pub fn new(source: [u8; 32], index: u64, code: MerkleErrorCode) -> Self {
        MerkleError {
            source,
            index,
            code,
        }
    }
}

impl fmt::Display for MerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MerkleError {:?} {:?} {:?}",
            self.source, self.index, self.code
        )
    }
}

impl Error for MerkleError {}

pub trait MerkleNode<H: Debug + Clone + PartialEq>: Clone {
    fn new_leaf(index: usize, data: &Vec<u8>) -> Self;
    fn hash(&self) -> H;
    fn set_hash(&mut self, hash: H);
    fn index(&self) -> u64;
    fn set(&mut self, data: &Vec<u8>);
    fn descendant(&self, index: usize) -> Option<H>;
    fn set_descendant(&mut self, index: usize, hash: H);
}

#[derive(Debug, Clone)]
pub struct MerkleProof<H: Debug + Clone + PartialEq, const D: usize> {
    pub source: H, // hash of the leaf data
    pub root: H,   // last is root
    pub assist: [H; D],
    pub index: u64,
}

/// get the offset of the node at its current level
/// 0
/// 1 2
/// 3 4 5 6
/// 7 8 9 10 11 12 13 14
/// get_offset(12) = 12 - 7 = 5
pub fn get_offset(index: u64) -> u64 {
    let height = (index + 1).ilog2();
    let full = (1u64 << height) - 1;
    index - full
}

pub fn binary_path_to_index(path: &[u64]) -> u64 {
    let offset = path.iter().fold(0, |acc, e| (acc << 1) + e);
    offset + (1u64 << path.len() - 1)
}

/// get a list of node index based on the binary path from root to leaf
pub fn binary_path_to_path(path: &[u64]) -> Vec<u64> {
    let mut ret = vec![];
    let mut acc = vec![];
    for c in path.iter() {
        acc.push(*c);
        ret.push(binary_path_to_index(acc.as_slice()));
    }
    ret
}

pub fn get_sibling_index(index: u64) -> u64 {
    if index % 2 == 1 {
        index + 1
    } else {
        index - 1
    }
}



pub trait MerkleTree<H: Debug + Clone + PartialEq, const D: usize> {
    type Node: MerkleNode<H>;

    fn hash(a: &H, b: &H) -> H;
    fn get_root_hash(&self) -> H;
    fn get_node_with_hash(&self, index: u64, hash: &H) -> Result<Self::Node, MerkleError>;
    fn update_root_hash(&mut self, hash: &H);
    fn chunk_depth() -> usize;

    fn hash_with_index(primary: &H, assist: &H, index: u64) -> H {
        let offset = get_offset(index);
        let (a, b) = if offset % 2 == 1 {
            (assist, primary)
        } else {
            (primary, assist)
        };
        Self::hash(a, b)
    }

    fn update_leaf(node: &mut Self::Node, path: &[u64], hash: H) {
        let mut node_idxs = binary_path_to_path(path);
        node_idxs.reverse();
        let mut new_hash = hash;
        for index in node_idxs {
            node.set_descendant(index as usize, new_hash.clone());
            let primary = node.descendant(index as usize);
            let assist = node.descendant(get_sibling_index(index) as usize);
            new_hash = Self::hash_with_index(&primary.unwrap(), &assist.unwrap(), index);
        };
        node.set_hash(new_hash);
    }

    fn boundary_check(&self, index: u64) -> Result<(), MerkleError> {
        if index >= (2_u64.pow(D as u32 + 1) - 1) {
            Err(MerkleError::new(
                [0; 32],
                index,
                MerkleErrorCode::InvalidIndex,
            ))
        } else {
            Ok(())
        }
    }

    ///
    /// Check that an index is a leaf.
    /// Example: Given D=2 and a merkle tree as follows:
    /// 0
    /// 1 2
    /// 3 4 5 6
    /// then leaf index >= 3 which is (2^D - 1)
    ///
    /// Moreover, nodes at depth k start at
    /// first = 2^k-1, last = 2^{k+1}-2
    ///
    fn leaf_check(&self, index: u64) -> Result<(), MerkleError> {
        if (index as u64) >= (2_u64.pow(D as u32) - 1)
            && (index as u64) < (2_u64.pow((D as u32) + 1) - 1)
        {
            Ok(())
        } else {
            Err(MerkleError::new(
                [0; 32],
                index,
                MerkleErrorCode::InvalidLeafIndex,
            ))
        }
    }

    /// get the index from leaf to the root
    /// root index is not included in the result as root index is always 0
    /// Example: Given D=3 and a merkle tree as follows:
    /// 0
    /// 1 2
    /// 3 4 5 6
    /// 7 8 9 10 11 12 13 14
    /// get_path(7) = [3, 1]
    /// get_path(14) = [6, 2]
    fn get_path(&self, index: u64) -> Result<[u64; D], MerkleError> {
        self.leaf_check(index)?;
        let mut height = (index + 1).ilog2();
        let round = height;
        let full = (1u64 << height) - 1;
        let mut p = index - full;
        let mut path = vec![];
        for _ in 0..round {
            let full = (1u64 << height) - 1;
            // Calculate the index of current node
            let i = full + p;
            path.insert(0, i);
            height = height - 1;
            // Caculate the offset of parent
            p = p / 2;
        }
        assert!(p == 0);
        Ok(path.try_into().unwrap())
    }

    fn get_path_binary(&self, index: u64) -> Result <[u64; D], MerkleError> {
        self.leaf_check(index)?;
        let height = (index + 1).ilog2();
        let round = height;
        let left_most = (1u64 << height) - 1;
        let mut c = index - left_most;
        let mut binary_path = vec![];
        for _ in 0..round {
            binary_path.push(c & 1);
            c = c >> 1;
        }
        binary_path.reverse();
        assert!(binary_path.len() == D);
        Ok(binary_path.try_into().unwrap())
    }

    /// Get the nodes and proof related to a leaf node with index
    /// the nodes starts from the root and all the way to the leaf
    fn trace_leaf_with_proof(
        &self,
        index: u64,
        update: Option<H>
    ) -> Result<(Vec<Self::Node>, MerkleProof<H, D>), MerkleError> {
        self.leaf_check(index)?;
        let paths = self.get_path_binary(index)?.to_vec();
        assert!((paths.len() % Self::chunk_depth()) == 0);
        let mut path_chunks = paths.chunks_exact(Self::chunk_depth()).collect::<Vec<&[u64]>>();

        // We start the search from the root hash
        let hash = self.get_root_hash();
        let root_node = self.get_node_with_hash(0, &hash)?;
        // nodes are from top to bottom
        let (assist, mut nodes) = path_chunks
            .iter()
            .fold(
                (vec![], vec![root_node]),
            |(mut assist, mut nodes), chunk| {
                let acc_node = nodes.last().unwrap().clone();
                let node_idxs = binary_path_to_path(chunk.to_vec().as_slice());
                let primary_hashs = node_idxs
                    .iter()
                    .map(|x| acc_node.descendant(*x as usize).unwrap())
                    .collect::<Vec<_>>();
                let mut sibling_hashs = node_idxs
                    .iter()
                    .map(|x| acc_node.descendant(get_sibling_index(*x) as usize).unwrap())
                    .collect::<Vec<_>>();

                let last_hash = primary_hashs.last().unwrap();
                let height = nodes.len() * Self::chunk_depth();
                let acc_node = self.get_node_with_hash(height as u64, last_hash).unwrap();
                nodes.push(acc_node);
                assist.append(&mut sibling_hashs);
                (assist, nodes)
            });

        let hash = nodes.last().unwrap().hash();

        if let Some(mut update_hash) = update {
            path_chunks.reverse();
            path_chunks.iter().fold(nodes.len() - 1, |acc, chunk| {
                let mut node = nodes.get_mut(acc - 1).unwrap();
                Self::update_leaf(&mut node, chunk, update_hash.clone());
                update_hash = node.hash();
                acc - 1
            });
        }

        assert!(assist.len() == D);

        Ok((
            nodes,
            MerkleProof {
                source: hash,
                root: self.get_root_hash(),
                assist: assist.try_into().unwrap(),
                index,
            },
        ))
    }

    fn get_leaf_with_proof(
        &self,
        index: u64,
    ) -> Result<(Self::Node, MerkleProof<H, D>), MerkleError> {
        let (mut nodes, proof) = self.trace_leaf_with_proof(index, None)?;
        return Ok((nodes.pop().unwrap(), proof))
    }


    fn update_nodes(&mut self, nodes: Vec<Self::Node>) -> Result<(), MerkleError>;

    fn set_leaf_with_proof(
        &mut self,
        leaf: &Self::Node,
    ) -> Result<MerkleProof<H, D>, MerkleError> {
        let index = leaf.index();
        let (mut nodes, mut proof) = self.trace_leaf_with_proof(index, Some(leaf.hash()))?;
        let hash = nodes[0].hash();
        self.update_root_hash(&hash);
        proof.root = hash;
        proof.source = leaf.hash();
        nodes.push(leaf.clone());
        self.update_nodes(nodes)?;
        return Ok(proof)
    }

    fn update_leaf_data_with_proof(
        &mut self,
        index: u64,
        data: &Vec<u8>,
    ) -> Result<MerkleProof<H, D>, MerkleError> {
        let node = Self::Node::new_leaf(index as usize, data);
        self.set_leaf_with_proof(&node)
    }

    fn verify_proof(&self, proof: &MerkleProof<H, D>) -> Result<bool, MerkleError> {
        let init = proof.source.clone();
        let mut p = get_offset(proof.index);
        let mut assist = proof.assist.clone();
        assist.reverse();

        let hash = assist.to_vec().iter().fold(init, |acc, x| {
            let (left, right) = if p % 2 == 1 { (x, &acc) } else { (&acc, x) };
            //println!("verify hash is {:?} {}, assist {:?}", acc, p % 2 == 1, x);
            p = p / 2;
            Self::hash(left, right)
        });
        //println!("root {:?}", proof.root);
        Ok(proof.root == hash)
    }
}

#[cfg(test)]
mod tests {
    use crate::host::merkle::{MerkleError, MerkleNode, MerkleTree};
    struct MerkleAsArray {
        data: [u64; 127], // 2^7-1 and depth = 6
        root_hash: u64,
    }

    impl MerkleAsArray {
        fn construct() -> Self {
            MerkleAsArray {
                data: [0 as u64; 127],
                root_hash: 0,
            }
        }

        fn debug(&self) {
            let mut start = 0;
            for i in 0..6 {
                let mut ns = vec![];
                for j in start..start + (1 << i) {
                    ns.push(self.data[j])
                }
                start = start + (1 << i);
                println!("dbg: {:?}", ns)
            }
        }

        fn get_child_index(index: u64) -> (u64, u64) {
            let left_child_index = (index + 1) * 2 - 1;
            let right_child_index = left_child_index + 1;
            (left_child_index, right_child_index)
        }

        pub fn height() -> u32 {
            return 6;
        }
    }

    #[derive(Clone)]
    struct MerkleU64Node {
        pub value: u64,
        pub index: u64,
        pub left: u64,
        pub right: u64,
    }

    impl MerkleNode<u64> for MerkleU64Node {
        fn set_descendant(&mut self, index: usize, v: u64) {
            if index == 0 {
                self.left = v;
            } else {
                self.right = v;
            }
        }
        fn set_hash(&mut self, v: u64) {
            self.value = v;
        }

        fn index(&self) -> u64 {
            self.index
        }
        fn hash(&self) -> u64 {
            self.value
        }
        fn set(&mut self, value: &Vec<u8>) {
            let v: [u8; 8] = value.clone().try_into().unwrap();
            self.value = u64::from_le_bytes(v);
        }

        fn new_leaf(index: usize, value: &Vec<u8>) -> MerkleU64Node {
            let v: [u8; 8] = value.clone().try_into().unwrap();
            MerkleU64Node {
                value: u64::from_le_bytes(v),
                index: index as u64,
                left: 0,
                right: 0,
            }
        }

        fn descendant(&self, i: usize) -> Option<u64> {
            if i==0 {
                Some(self.left)
            } else if i==1 {
                Some(self.right)
            } else {
                None
            }
        }
    }

    impl MerkleTree<u64, 6> for MerkleAsArray {
        type Node = MerkleU64Node;

        fn hash(a: &u64, b: &u64) -> u64 {
            a + b
        }

        fn chunk_depth() -> usize {
            1
        }

        fn get_root_hash(&self) -> u64 {
            return self.data[0];
        }

        fn update_root_hash(&mut self, hash: &u64) {
            self.root_hash = hash.clone();
        }

        fn update_nodes(&mut self, nodes: Vec<Self::Node>) -> Result<(), MerkleError> {
            for node in nodes.into_iter() {
                self.data[node.index() as usize] = node.value;
            }
            Ok (())
        }

        fn get_node_with_hash(&self, index: u64, _hash: &u64) -> Result<Self::Node, MerkleError> {
            self.boundary_check(index)?;

            let height = (index + 1).ilog2();
            let mut left_val: u64 = 0;
            let mut right_val: u64 = 0;
            if height < Self::height() {
                // not leaf node
                let (left_child_index, right_child_index) = MerkleAsArray::get_child_index(index);
                left_val = self.data[left_child_index as usize];
                right_val = self.data[right_child_index as usize];
            }
            Ok(MerkleU64Node {
                value: self.data[index as usize],
                index,
                left: left_val,
                right: right_val,
            })
        }
    }

    #[test]
    fn test_merkle_path() {
        let mut mt = MerkleAsArray::construct();
        let (mut leaf, _) = mt.get_leaf_with_proof(2_u64.pow(6) - 1).unwrap();
        leaf.value = 1;
        let _proof = mt.set_leaf_with_proof(&leaf).unwrap();

        /* one update of 1 is 1 */
        let root = mt.get_root_hash();
        mt.debug();
        assert_eq!(root, 1 as u64);

        let (mut leaf, _) = mt.get_leaf_with_proof(2_u64.pow(6) + 2).unwrap();
        leaf.value = 2;
        let _proof = mt.set_leaf_with_proof(&leaf).unwrap();

        /* two leaves hash needs to be 3 */
        let root = mt.get_root_hash();
        mt.debug();
        assert_eq!(root, 3 as u64);

        let (mut leaf, _) = mt.get_leaf_with_proof(2_u64.pow(6) + 4).unwrap();
        leaf.value = 3;
        let _proof = mt.set_leaf_with_proof(&leaf).unwrap();
        /* two leaves hash needs to be 3 */
        let root = mt.get_root_hash();
        mt.debug();
        assert_eq!(root, 6 as u64);
    }
}
