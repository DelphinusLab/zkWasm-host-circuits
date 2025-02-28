use std::cell::RefCell;
use std::rc::Rc;

use ff::PrimeField;
use halo2_proofs::pairing::bn256::Fr;
use lazy_static;
use mongodb::bson::doc;
use mongodb::bson::{spec::BinarySubtype, Bson};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::host::db::{MongoDB, TreeDB};
use crate::host::merkle::{MerkleError, MerkleErrorCode, MerkleNode, MerkleProof, MerkleTree};
use crate::host::poseidon::MERKLE_HASHER;
use crate::host::poseidon::MERKLE_LEAF_HASHER;

fn deserialize_u256_as_binary<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok(bytes.bytes.try_into().unwrap()),
        Ok(..) => Err(Error::invalid_value(Unexpected::Enum, &"Bson::Binary")),
        Err(e) => Err(e),
    }
}

fn deserialize_bytes_from_binary<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok(bytes.bytes.to_vec()),
        Ok(..) => Err(Error::invalid_value(Unexpected::Enum, &"Bson::Binary")),
        Err(e) => Err(e),
    }
}

fn serialize_bytes_as_binary<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let binary = Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: bytes.into(),
    });
    binary.serialize(serializer)
}

fn deserialize_option_u256_as_binary<'de, D>(deserializer: D) -> Result<Option<[u8; 32]>, D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok(Some(bytes.bytes.try_into().unwrap())),
        Ok(Bson::Null) => Ok(None),
        Ok(..) => Err(Error::invalid_value(Unexpected::Enum, &"Bson::Binary")),
        Err(e) => Err(e),
    }
}

fn serialize_option_bytes_as_binary<S>(
    bytes: &Option<[u8; 32]>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match bytes {
        Some(bytes) => {
            let binary = Bson::Binary(mongodb::bson::Binary {
                subtype: BinarySubtype::Generic,
                bytes: bytes.to_vec(),
            });
            binary.serialize(serializer)
        }
        None => serializer.serialize_none(),
    }
}

#[derive(Clone)]
pub struct MongoMerkle<const DEPTH: usize> {
    root_hash: [u8; 32],
    default_hash: Vec<[u8; 32]>,
    db: Rc<RefCell<dyn TreeDB>>,
}

impl PartialEq for MerkleRecord {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.hash == other.hash
    }
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl<const DEPTH: usize> MongoMerkle<DEPTH> {
    pub fn get_record(&self, hash: &[u8; 32]) -> Result<Option<MerkleRecord>, anyhow::Error> {
        self.db.borrow().get_merkle_record(hash)
    }

    /* We always insert new record as there might be uncommitted update to the merkle tree */
    pub fn update_record(&mut self, record: MerkleRecord) -> Result<(), anyhow::Error> {
        let exists = self.get_record(&record.hash);
        //println!("record is none: {:?}", exists.as_ref().unwrap().is_none());
        exists.map_or_else(
            |e| Err(e),
            |r: Option<MerkleRecord>| {
                r.map_or_else(
                    || {
                        //println!("Do update record to DB for index {:?}, hash: {:?}", record.index, record.hash);
                        self.db.borrow_mut().set_merkle_record(record)?;
                        Ok(())
                    },
                    |_| Ok(()),
                )
            },
        )
    }

    //the input records must be in one leaf path
    pub fn update_records(&mut self, records: &Vec<MerkleRecord>) -> Result<(), anyhow::Error> {
        /*
        for r in records.iter() {
            println!("update record: {:?}", r.hash());
        }
        */
        self.db.borrow_mut().set_merkle_records(records)?;
        Ok(())
    }

    pub fn get_node_default_hash(&self, height: usize) -> [[u8; 32]; CHUNK_DEPTH] {
        let mut default_hash = vec![];
        for i in 0..CHUNK_DEPTH {
            let hash = self.get_default_hash(height + i + 1).unwrap();
            default_hash.push(hash);
        }
        default_hash.try_into().unwrap()
    }

    pub fn generate_default_node(&self, index: u64) -> Result<MerkleRecord, MerkleError> {
        let height = (index + 1).ilog2() as usize;
        let default_hash = if height < Self::height() {
            Some(self.get_node_default_hash(height as usize))
        } else {
            assert!(height == Self::height());
            None
        };
        Ok(MerkleRecord {
            index,
            default_hash,
            hash: self.get_default_hash(height)?,
            data: None,
            descendants: vec![]
        })
    }

    pub fn check_generate_default_node(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<MerkleRecord, MerkleError> {
        let node = self.generate_default_node(index)?;
        if node.hash() == *hash {
            Ok(node)
        } else {
            Err(MerkleError::new(*hash, index, MerkleErrorCode::InvalidHash))
        }
    }

    fn generate_or_get_node(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<MerkleRecord, MerkleError> {
        let height = (index + 1).ilog2() as usize;
        assert!(height <= Self::height());
        let default_hash = self.get_default_hash(height)?;
        if &default_hash == hash {
            self.generate_default_node(index)
        } else {
            match self.get_record(hash) {
                Ok(Some(mut node)) => {
                    // The index of MerkleRecord was not stored in db, so it needs to be assigned here.
                    node.index = index;
                    if height != Self::height() {
                        node.default_hash = Some(self.get_node_default_hash(height as usize))
                    };
                    Ok(node)
                }
                Ok(None) => Err(MerkleError::new(
                    *hash,
                    index,
                    MerkleErrorCode::RecordNotFound,
                )),
                Err(_) => Err(MerkleError::new(
                    *hash,
                    index,
                    MerkleErrorCode::UnexpectedDBError,
                )),
            }
        }
    }
}

const CHUNK_DEPTH: usize = 4;
const CHUNK_VOLUME: usize = 31;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MerkleRecord {
    // The index will not to be stored in db.
    #[serde(skip_serializing, skip_deserializing, default)]
    pub index: u64,
    #[serde(skip_serializing, skip_deserializing, default)]
    pub default_hash: Option<[[u8; 32]; CHUNK_DEPTH]>,
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    #[serde(rename = "_id")]
    pub hash: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_bytes_from_binary")]
    pub descendants: Vec<u8>, // 2^4 - 1 - 1 (root)
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "self::serialize_option_bytes_as_binary",
        default
    )]
    #[serde(deserialize_with = "self::deserialize_option_u256_as_binary")]
    pub data: Option<[u8; 32]>,
}

impl MerkleNode<[u8; 32]> for MerkleRecord {
    fn index(&self) -> u64 {
        self.index
    }

    fn hash(&self) -> [u8; 32] {
        self.hash
    }

    fn set_hash(&mut self, hash: [u8; 32]) {
        self.hash = hash;
    }

    fn set_descendant(&mut self, index: usize, hash: [u8; 32]) {
        for c in 0..CHUNK_VOLUME {
            if c * 33 < self.descendants.len() {
                if self.descendants[c*33] == index as u8 {
                    for i in 0..32 {
                        let offset = c * 33 + i + 1;
                        self.descendants[offset] = hash[i];
                    }
                    return;
                }
            }
        }
        self.descendants.push(index as u8);
        for h in hash.to_vec().iter() {
            self.descendants.push(*h);
        }
    }

    fn new_leaf(index: usize, data: &Vec<u8>) -> Self{
        let mut leaf = MerkleRecord::new(index as u64);
        leaf.set(data);
        return leaf
    }
    fn set(&mut self, data: &Vec<u8>) {
        let mut hasher = MERKLE_LEAF_HASHER.clone();
        self.data = Some(data.clone().try_into().unwrap());
        let batchdata = data
            .chunks(16)
            .into_iter()
            .map(|x| {
                let mut v = x.to_vec();
                v.extend_from_slice(&[0u8; 16]);
                let f = v.try_into().unwrap();
                Fr::from_repr(f).unwrap()
            })
            .collect::<Vec<Fr>>();
        let values: [Fr; 2] = batchdata.try_into().unwrap();

        self.hash = hasher.update_exact(&values).to_repr();
        //println!("update with values {:?}", values);
        //println!("update with new hash {:?}", self.hash);
    }
    fn descendant(&self, offset: usize ) -> Option<[u8; 32]> {
        for c in 0..CHUNK_VOLUME {
            if c * 33 < self.descendants.len() {
                if self.descendants[c*33] == offset as u8 {
                    let offset = c * 33 + 1;
                    let r = self.descendants[offset .. offset + 32].to_vec();
                    return Some(r.try_into().unwrap())
                }
            }
        }
        let index = offset + 1;
        let height = (index + 1).ilog2() as usize;
        //println!("offset is {} {} {}", offset, height, self.descendants.len());
        return self.default_hash.map(
            |d| d[height - 1]
        );
    }
}

impl MerkleRecord {
    fn new(index: u64) -> Self {
        MerkleRecord {
            index,
            default_hash: None,
            hash: [0; 32],
            data: None,
            descendants: vec![],
        }
    }

    pub fn data_as_u64(&self) -> [u64; 4] {
        let data = self.data.unwrap_or([0; 32]);
        [
            u64::from_le_bytes(data[0..8].try_into().unwrap()),
            u64::from_le_bytes(data[8..16].try_into().unwrap()),
            u64::from_le_bytes(data[16..24].try_into().unwrap()),
            u64::from_le_bytes(data[24..32].try_into().unwrap()),
        ]
    }
}

impl<const DEPTH: usize> MongoMerkle<DEPTH> {
    pub fn height() -> usize {
        return DEPTH;
    }

    pub fn construct(addr: [u8; 32], root: [u8; 32], db: Option<Rc<RefCell<dyn TreeDB>>>) -> Self {
        MongoMerkle {
            root_hash: root,
            default_hash: DEFAULT_HASH_VEC.clone(),
            db: db.unwrap_or_else(|| Rc::new(RefCell::new(MongoDB::new(addr, None)))),
        }
    }

    fn empty_leaf(index: u64) -> MerkleRecord {
        let mut leaf = MerkleRecord::new(index);
        leaf.set(&[0; 32].to_vec());
        leaf
    }

    /// depth start from 0 up to Self::height(). Example 20 height MongoMerkle, root depth=0, leaf depth=20
    pub fn get_default_hash(&self, depth: usize) -> Result<[u8; 32], MerkleError> {
        if depth <= Self::height() {
            Ok(self.default_hash[Self::height() - depth])
        } else {
            Err(MerkleError::new(
                [0; 32],
                depth as u64,
                MerkleErrorCode::InvalidDepth,
            ))
        }
    }

    pub fn default_proof(&self) -> MerkleProof<[u8; 32], DEPTH> {
        let mut assist = [0; DEPTH];
        for i in 0..DEPTH {
            assist[i] = i;
        }
        MerkleProof {
            source: self.get_default_hash(DEPTH).unwrap(),
            root: self.get_default_hash(0).unwrap(),
            assist: assist.map(|x| self.get_default_hash(x + 1).unwrap()),
            index: (1_u64 << DEPTH) - 1,
        }
    }
}

// In default_hash vec, it is from leaf to root.
// For example, suppose that the height of merkle tree is 20.
// DEFAULT_HASH_VEC[0] represents the default leaf hash.
// DEFAULT_HASH_VEC[20] is root default hash.
// It has 21 layers including the leaf layer and root layer.
lazy_static::lazy_static! {
    pub static ref DEFAULT_HASH_VEC: Vec<[u8; 32]> = {
        let mut leaf_hash = MongoMerkle::<64>::empty_leaf(0).hash;
        let mut default_hash = vec![leaf_hash];
        for _ in 0..(MongoMerkle::<64>::height()) {
            leaf_hash = MongoMerkle::<64>::hash(&leaf_hash, &leaf_hash);
            default_hash.push(leaf_hash);
        }
        default_hash
    };
}

impl<const DEPTH: usize> MerkleTree<[u8; 32], DEPTH> for MongoMerkle<DEPTH> {
    type Node = MerkleRecord;

    fn get_root_hash(&self) -> [u8; 32] {
        self.root_hash
    }

    fn chunk_depth() -> usize {
        CHUNK_DEPTH
    }

    fn update_root_hash(&mut self, hash: &[u8; 32]) {
        self.root_hash = hash.clone();
    }

    fn hash(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
        let mut hasher = MERKLE_HASHER.clone();
        let a = Fr::from_repr(*a).unwrap();
        let b = Fr::from_repr(*b).unwrap();
        hasher.update_exact(&[a, b]).to_repr()
    }

    fn update_nodes(
        &mut self,
        nodes: Vec<MerkleRecord>
    ) -> Result<(), MerkleError> {
        self.update_records(&nodes)
            .expect("Unexpected DB Error when update records.");
        Ok(())
    }

    fn get_node_with_hash(&self, index: u64, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        self.generate_or_get_node(index, hash)
    }
}

impl<const DEPTH: usize> MongoMerkle<DEPTH> {
    pub fn default() -> Self {
        let addr = [0u8; 32];
        MongoMerkle {
            root_hash: DEFAULT_HASH_VEC[DEPTH],
            default_hash: (*DEFAULT_HASH_VEC).clone(),
            db: Rc::new(RefCell::new(MongoDB::new(addr, None))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{MerkleRecord, MongoMerkle, DEFAULT_HASH_VEC};
    use crate::host::db::{
        get_collection, get_collection_name, MongoDB, MONGODB_DATABASE, MONGODB_DATA_NAME_PREFIX,
    };
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::utils::{bytes_to_u64, field_to_bytes};
    use halo2_proofs::pairing::bn256::Fr;
    use mongodb::bson::doc;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    /* Test for check parent node
     * 1. Clear m tree collection. Create default empty m tree. Check root.
     * 2. Update index=2_u32.pow(32) - 1 (first leaf) leave value.
     * 3. Update index=2_u32.pow(32) (second leaf) leave value.
     * 4. Get index=2_u32.pow(30) - 1 node with hash and confirm the left and right are previous set leaves.
     * 5. Load mt from DB and Get index=2_u32.pow(19) - 1 node with hash and confirm the left and right are previous set leaves.
     */
    fn test_mongo_merkle_parent_node() {
        const DEPTH: usize = 32;
        const TEST_ADDR: [u8; 32] = [1; 32];
        let index = 2_u64.pow(DEPTH as u32) - 1;
        let data = Fr::from(0x1000 as u64);
        println!(
            "depth 32 default root is {:?}",
            bytes_to_u64(&DEFAULT_HASH_VEC[DEPTH])
        );

        let mongodb = Rc::new(RefCell::new(MongoDB::new(TEST_ADDR, None)));

        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(mongodb.clone()),
        );
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);

        let (mut leaf, proof) = mt.get_leaf_with_proof(index).unwrap();
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
        let bytesdata = field_to_bytes(&data).to_vec();
        leaf.set(&bytesdata);
        let proof = mt.set_leaf_with_proof(&leaf).unwrap();
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
    }

    #[test]
    fn show_default_root() {
        println!("default root in bytes {:?}", DEFAULT_HASH_VEC[32]);
        println!(
            "default root in u64 {:?}",
            bytes_to_u64(&DEFAULT_HASH_VEC[32])
        );
    }

    #[test]
    /* Basic tests for 32 height m tree
     * 1. Update index=2_u32.pow(32) - 1 (first leaf) leave value. Check root.
     * 2. Check index=2_u32.pow(32) - 1 leave value updated.
     * 3. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_single_leaf_update() {
        // Init checking results
        const DEPTH: usize = 32;
        const TEST_ADDR: [u8; 32] = [2; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32);// - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        let mongodb = Rc::new(RefCell::new(MongoDB::new(TEST_ADDR, None)));

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(mongodb.clone()),
        );
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);

        // 3
        let a = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(TEST_ADDR, a, None);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
    }

    #[test]
    /* Like the above test but use 16 depth
     * 1. Update index=2_u32.pow(16) - 1 (first leaf) leave value. Check root.
     * 2. Check index=2_u32.pow(16) - 1 leave value updated.
     * 3. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_single_leaf_update_16_depth() {
        // Init checking results
        const DEPTH: usize = 16;
        const TEST_ADDR: [u8; 32] = [4; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32); // - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        let mongodb = Rc::new(RefCell::new(MongoDB::new(TEST_ADDR, None)));

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(mongodb.clone()),
        );
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);

        // 3
        let a = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(TEST_ADDR, a, None);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
    }


    fn test_mongo_merkle_multi_leaves_update_16_depth(offset: u64) {
        // Init checking results
        const DEPTH: usize = 16;
        const TEST_ADDR: [u8; 32] = [4; 32];
        let magic_number = offset * offset;

        let mongodb = Rc::new(RefCell::new(MongoDB::new(TEST_ADDR, None)));

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(mongodb.clone()),
        );
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);

        for i in offset..offset + 128 {
            let full_index: u64 = 2_u64.pow(DEPTH as u32) - 1 + (i % 2_u64.pow(DEPTH as u32));
            let data_index = (full_index % 32) as usize;
            let mut data = [0; 32];
            data[data_index] = (full_index % 256) as u8 + 1;
            let (mut leaf, _) = mt.get_leaf_with_proof(full_index).unwrap();

            leaf.set(&data.to_vec());
            mt.set_leaf_with_proof(&leaf).unwrap();

            let (leaf, _) = mt.get_leaf_with_proof(full_index).unwrap();
            assert_eq!(leaf.index, full_index);
            assert_eq!(leaf.data.unwrap(), data);
        }

        // recheck
        for i in offset..offset + 128 {
            let full_index: u64 = 2_u64.pow(DEPTH as u32) - 1_u64 + (i % 2_u64.pow(DEPTH as u32));
            let data_index = (full_index % 32) as usize;
            let mut data = [0; 32];
            data[data_index] = (full_index % 256) as u8 + 1;
            let (leaf, proof) = mt.get_leaf_with_proof(full_index).unwrap();
            assert_eq!(leaf.index, full_index);
            assert_eq!(leaf.data.unwrap(), data);
            let verified = mt.verify_proof(&proof).unwrap();
            assert_eq!(true, verified);
        }
    }

    #[test]
    /* Like the above test but use 16 depth
     * 1. Update index=2_u32.pow(16) - 1 (first leaf) leave value. Check root.
     * 2. Check index=2_u32.pow(16) - 1 leave value updated.
     * 3. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_multi_leaves_16_depth() {
        for i in 0..32 {
            test_mongo_merkle_multi_leaves_update_16_depth(i+1);
        }
    }



    /* Tests for 32 height m tree with updating multple leaves
     * 1. Clear m tree collection. Create default empty m tree. Check root (default one, A).
     * 2. Update index=2_u32.pow(32) - 1 (first leaf) leave value. Check root (1 leave updated, B). Check index=2_u32.pow(20) - 1 leave value updated.
     * 3. Update index=2_u32.pow(32) (second leaf) leave value. Check root (1 leave updated, C). Check index=2_u32.pow(20) leave value updated.
     * 4. Update index=2_u32.pow(22) - 2 (last leaf) leave value. Check root (1 leave updated, D). Check index=2_u32.pow(21) -2 leave value updated.
     * 5. Load m tree from DB with D root hash, check root and leaves' values.
     */
    fn _test_mongo_merkle_multi_leaves_update(addr: u8) {
        // Init checking results
        const DEPTH: usize = 32;
        let test_addr: [u8; 32] = [addr; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const INDEX2: u64 = 2_u64.pow(DEPTH as u32);
        const LEAF2_DATA: [u8; 32] = [
            0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const INDEX3: u64 = 2_u64.pow((DEPTH + 1) as u32) - 2;
        const LEAF3_DATA: [u8; 32] = [
            18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        let mongodb = Rc::new(RefCell::new(MongoDB::new(test_addr, None)));

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(
            test_addr,
            DEFAULT_HASH_VEC[DEPTH],
            Some(mongodb.clone()),
        );
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), test_addr);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);
        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();

        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);

        // 3
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        leaf.set(&LEAF2_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data.unwrap(), LEAF2_DATA);

        // 4
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        leaf.set(&LEAF3_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data.unwrap(), LEAF3_DATA);

        // 5
        let root = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(test_addr, root, None);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);
        assert!(mt.verify_proof(&proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data.unwrap(), LEAF2_DATA);
        assert!(mt.verify_proof(&proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data.unwrap(), LEAF3_DATA);
        assert!(mt.verify_proof(&proof).unwrap());
    }

    #[test]
    fn test_mongo_merkle_multi_leaves_update() {
        _test_mongo_merkle_multi_leaves_update(3);
    }

    #[test]
    /* Tests cache hit
     * Please note this test logic is to delete the records in DB for the second run and all depends on cache.
     */
    fn test_cache_hit() {
        for _ in 0..2 {
            _test_mongo_merkle_multi_leaves_update(5);
        }
    }

    #[test]
    /* Test duplicate update same leaf with same data for 32 height m tree
     * 1. Update index=2_u32.pow(32) - 1 (first leaf) leaf value. Check root.
     * 2. Check index=2_u32.pow(32) - 1 leave value updated.
     * 3. Update index=2_u32.pow(32) - 1 (first leaf) leaf value. Check root.
     * 4. Check index=2_u32.pow(32) - 1 leave value updated.
     * 5. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_duplicate_leaf_update() {
        // Init checking results
        const DEPTH: usize = 32;
        const TEST_ADDR: [u8; 32] = [6; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        let mongodb = Rc::new(RefCell::new(MongoDB::new(TEST_ADDR, None)));
        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH],
            Some(mongodb.clone()),
        );

        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection = get_collection::<MerkleRecord>(
            mongodb.borrow().get_database_client().unwrap(),
            MONGODB_DATABASE.to_string(),
            cname,
        )
        .unwrap();
        let _ = collection.delete_many(doc! {}, None);


        // 1
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        // 2
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);

        // 3
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        // 4
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);

        // 5
        let a = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(TEST_ADDR, a, None);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data.unwrap(), LEAF1_DATA);
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
    }
}
