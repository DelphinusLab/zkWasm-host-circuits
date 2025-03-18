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

use crate::host::db::{MongoDB, RocksDB, TreeDB};
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
        self.db.borrow_mut().set_merkle_records(records)?;
        Ok(())
    }

    pub fn generate_default_node(&self, index: u64) -> Result<MerkleRecord, MerkleError> {
        let height = (index + 1).ilog2();
        let default = self.get_default_hash(height as usize)?;
        let child_hash = if height == Self::height() as u32 {
            None
        } else {
            let hash = self.get_default_hash((height + 1) as usize)?;
            Some(hash)
        };

        Ok(MerkleRecord {
            index,
            hash: default,
            data: None,
            left: child_hash,
            right: child_hash,
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
        let height = (index + 1).ilog2();
        let default_hash = self.get_default_hash(height as usize)?;
        if &default_hash == hash {
            self.generate_default_node(index)
        } else {
            match self.get_record(hash) {
                Ok(Some(mut node)) => {
                    // The index of MerkleRecord was not stored in db, so it needs to be assigned here.
                    node.index = index;
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

    fn start_record(&self, record_db: RocksDB) -> anyhow::Result<()> {
        self.db.borrow_mut().start_record(record_db)
    }

    fn stop_record(&self) -> anyhow::Result<RocksDB> {
        self.db.borrow_mut().stop_record()
    }

    fn is_recording(&self) -> bool {
        self.db.borrow().is_recording()
    }
}

pub type RocksMerkle<const DEPTH: usize> = MongoMerkle<DEPTH>;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MerkleRecord {
    // The index will not to be stored in db.
    #[serde(skip_serializing, skip_deserializing, default)]
    pub index: u64,
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    #[serde(rename = "_id")]
    pub hash: [u8; 32],
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "self::serialize_option_bytes_as_binary",
        default
    )]
    #[serde(deserialize_with = "self::deserialize_option_u256_as_binary")]
    pub left: Option<[u8; 32]>,
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "self::serialize_option_bytes_as_binary",
        default
    )]
    #[serde(deserialize_with = "self::deserialize_option_u256_as_binary")]
    pub right: Option<[u8; 32]>,
    #[serde(
        skip_serializing_if = "Option::is_none",
        serialize_with = "self::serialize_option_bytes_as_binary",
        default
    )]
    #[serde(deserialize_with = "self::deserialize_option_u256_as_binary")]
    pub data: Option<[u8; 32]>,
}

impl MerkleRecord {
    /// serialize MerkleRecord to Vec<u8> \
    /// Note: index can be ignored as it is not stored in db.
    pub fn to_slice(&self) -> Vec<u8> {
        let mut result = Vec::new();

        // hash ([u8; 32])
        result.extend_from_slice(&self.hash);

        // left (Option<[u8; 32]>)
        if let Some(left) = self.left {
            result.push(1); // 表示Some
            result.extend_from_slice(&left);
        } else {
            result.push(0); // 表示None
        }

        // right (Option<[u8; 32]>)
        if let Some(right) = self.right {
            result.push(1);
            result.extend_from_slice(&right);
        } else {
            result.push(0);
        }

        // data (Option<[u8; 32]>)
        if let Some(data) = self.data {
            result.push(1);
            result.extend_from_slice(&data);
        } else {
            result.push(0);
        }

        result
    }

    /// deserialize Vec<u8> to MerkleRecord
    pub fn from_slice(slice: &[u8]) -> Result<Self, anyhow::Error> {
        if slice.len() < 8 {
            return Err(anyhow::anyhow!("Slice too short for index"));
        }

        let mut pos = 0;

        // hash
        if slice.len() < pos + 32 {
            return Err(anyhow::anyhow!("Slice too short for hash"));
        }
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&slice[pos..pos+32]);
        pos += 32;

        // left
        if slice.len() < pos + 1 {
            return Err(anyhow::anyhow!("Slice too short for left flag"));
        }
        let left = match slice[pos] {
            0 => {
                pos += 1;
                None
            },
            1 => {
                pos += 1;
                if slice.len() < pos + 32 {
                    return Err(anyhow::anyhow!("Slice too short for left value"));
                }
                let mut left_val = [0u8; 32];
                left_val.copy_from_slice(&slice[pos..pos+32]);
                pos += 32;
                Some(left_val)
            },
            _ => return Err(anyhow::anyhow!("Invalid left flag")),
        };

        // right
        if slice.len() < pos + 1 {
            return Err(anyhow::anyhow!("Slice too short for right flag"));
        }
        let right = match slice[pos] {
            0 => {
                pos += 1;
                None
            },
            1 => {
                pos += 1;
                if slice.len() < pos + 32 {
                    return Err(anyhow::anyhow!("Slice too short for right value"));
                }
                let mut right_val = [0u8; 32];
                right_val.copy_from_slice(&slice[pos..pos+32]);
                pos += 32;
                Some(right_val)
            },
            _ => return Err(anyhow::anyhow!("Invalid right flag")),
        };

        // data
        if slice.len() < pos + 1 {
            return Err(anyhow::anyhow!("Slice too short for data flag"));
        }
        let data = match slice[pos] {
            0 => {
                // pos += 1;
                None
            },
            1 => {
                pos += 1;
                if slice.len() < pos + 32 {
                    return Err(anyhow::anyhow!("Slice too short for data value"));
                }
                let mut data_val = [0u8; 32];
                data_val.copy_from_slice(&slice[pos..pos+32]);
                Some(data_val)
            },
            _ => return Err(anyhow::anyhow!("Invalid data flag")),
        };

        Ok(MerkleRecord {
            index: 0, // Deserialize index as 0 since it is not stored in db
            hash,
            left,
            right,
            data,
        })
    }
}


impl MerkleNode<[u8; 32]> for MerkleRecord {
    fn index(&self) -> u64 {
        self.index
    }
    fn hash(&self) -> [u8; 32] {
        self.hash
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

        cfg_if::cfg_if! {
            if #[cfg(feature="complex-leaf")] {
                hasher.update(&values);
                self.hash = hasher.squeeze().to_repr();
            } else {
                self.hash = hasher.update_exact(&values).to_repr();
            }
        }
        //println!("update with values {:?}", values);
        //println!("update with new hash {:?}", self.hash);
    }
    fn right(&self) -> Option<[u8; 32]> {
        self.right
    }
    fn left(&self) -> Option<[u8; 32]> {
        self.left
    }
}

impl MerkleRecord {
    fn new(index: u64) -> Self {
        MerkleRecord {
            index,
            hash: [0; 32],
            data: None,
            left: None,
            right: None,
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
    type Id = [u8; 32];
    type Root = [u8; 32];
    type Node = MerkleRecord;

    fn construct(addr: Self::Id, root: Self::Root, db: Option<Rc<RefCell<dyn TreeDB>>>) -> Self {
        MongoMerkle {
            root_hash: root,
            default_hash: DEFAULT_HASH_VEC.clone(),
            db: db.unwrap_or_else(|| Rc::new(RefCell::new(MongoDB::new(addr, None)))),
        }
    }

    fn get_root_hash(&self) -> [u8; 32] {
        self.root_hash
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

    fn set_parent(
        &mut self,
        index: u64,
        hash: &[u8; 32],
        left: &[u8; 32],
        right: &[u8; 32],
    ) -> Result<(), MerkleError> {
        self.boundary_check(index)?;
        let record = MerkleRecord {
            index,
            data: None,
            left: Some(*left),
            right: Some(*right),
            hash: *hash,
        };
        //println!("set_node_with_hash {} {:?}", index, hash);
        self.update_record(record).expect("Unexpected DB Error");
        Ok(())
    }

    fn set_leaf_and_parents(
        &mut self,
        leaf: &MerkleRecord,
        parents: [(u64, [u8; 32], [u8; 32], [u8; 32]); DEPTH],
    ) -> Result<(), MerkleError> {
        self.leaf_check(leaf.index)?;
        let mut records: Vec<MerkleRecord> = parents
            .iter()
            .filter_map(|(index, hash, left, right)| {
                let height = (index + 1).ilog2();
                match self.get_default_hash(height as usize) {
                    // There is no need to set default nodes in db.
                    Ok(default_hash) if hash != &default_hash => Some(MerkleRecord {
                        index: *index,
                        data: None,
                        left: Some(*left),
                        right: Some(*right),
                        hash: *hash,
                    }),
                    _ => None,
                }
            })
            .collect();

        records.push(leaf.clone());
        self.update_records(&records)
            .expect("Unexpected DB Error when update records.");

        Ok(())
    }

    fn get_node_with_hash(&self, index: u64, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        self.generate_or_get_node(index, hash)
    }

    fn set_leaf(&mut self, leaf: &MerkleRecord) -> Result<(), MerkleError> {
        self.leaf_check(leaf.index())?;
        self.update_record(leaf.clone())
            .expect("Unexpected DB Error");
        Ok(())
    }

    fn get_leaf_with_proof(
        &self,
        index: u64,
    ) -> Result<(Self::Node, MerkleProof<[u8; 32], DEPTH>), MerkleError> {
        self.leaf_check(index)?;
        let paths = self.get_path(index)?.to_vec();
        // We push the search from the top
        let hash = self.get_root_hash();
        let mut acc = 0;
        let mut acc_node = self.generate_or_get_node(acc, &hash)?;
        let assist: Vec<[u8; 32]> = paths
            .into_iter()
            .map(|child| {
                let (hash, sibling_hash) = if (acc + 1) * 2 == child + 1 {
                    // left child
                    (acc_node.left().unwrap(), acc_node.right().unwrap())
                } else {
                    assert_eq!((acc + 1) * 2, child);
                    (acc_node.right().unwrap(), acc_node.left().unwrap())
                };
                acc = child;
                acc_node = self.generate_or_get_node(acc, &hash)?;
                Ok(sibling_hash)
            })
            .collect::<Result<Vec<[u8; 32]>, _>>()?;
        let hash = acc_node.hash();
        Ok((
            acc_node,
            MerkleProof {
                source: hash,
                root: self.get_root_hash(),
                assist: assist.try_into().unwrap(),
                index,
            },
        ))
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
    use super::{MerkleRecord, MongoMerkle, DEFAULT_HASH_VEC, RocksMerkle};
    use crate::host::db::{get_collection, get_collection_name, MongoDB, MONGODB_DATABASE, MONGODB_DATA_NAME_PREFIX, RocksDB};
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::utils::{bytes_to_u64, field_to_bytes};
    use halo2_proofs::pairing::bn256::Fr;
    use mongodb::bson::doc;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::time::Instant;

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
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32) - 1;
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
    /* Like the above test but use 13 depth
     * 1. Update index=2_u32.pow(13) - 1 (first leaf) leave value. Check root.
     * 2. Check index=2_u32.pow(13) - 1 leave value updated.
     * 3. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_single_leaf_update_13_depth() {
        // Init checking results
        const DEPTH: usize = 13;
        const TEST_ADDR: [u8; 32] = [4; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32) - 1;
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

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(mongodb.clone()),
        );

        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection =
            get_collection::<MerkleRecord>(
                mongodb.borrow().get_database_client().unwrap(),
                MONGODB_DATABASE.to_string(),
                cname
            ).unwrap();
        let _ = collection.delete_many(doc! {}, None);

        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        // 2
        let start = Instant::now();
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        let duration = start.elapsed();
        println!("get_leaf_with_proof elapse: {} us", duration.as_micros());
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

    #[test]
    /* Test duplicate update same leaf with same data for 32 height m tree
     * 1. Update index=2_u32.pow(32) - 1 (first leaf) leaf value. Check root.
     * 2. Check index=2_u32.pow(32) - 1 leave value updated.
     * 3. Update index=2_u32.pow(32) - 1 (first leaf) leaf value. Check root.
     * 4. Check index=2_u32.pow(32) - 1 leave value updated.
     * 5. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_duplicate_leaf_update_with_rocksdb() {
        // Init checking results
        const DEPTH: usize = 32;
        const TEST_ADDR: [u8; 32] = [6; 32];
        const INDEX1: u64 = 2_u64.pow(DEPTH as u32) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];


        let rocks_db = Rc::new(RefCell::new(RocksDB::new("./test_db/").unwrap()));

        // 1
        let mut mt = RocksMerkle::<DEPTH>::construct(
            TEST_ADDR,
            DEFAULT_HASH_VEC[DEPTH].clone(),
            Some(rocks_db.clone()),
        );

        let _ = rocks_db.borrow_mut().clear();


        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        // 2
        let start = Instant::now();
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        let duration = start.elapsed();
        println!("get_leaf_with_proof elapse: {} us", duration.as_micros());
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
