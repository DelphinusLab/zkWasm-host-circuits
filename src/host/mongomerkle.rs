use crate::host::cache::MERKLE_CACHE;
use crate::host::db;
use crate::host::db::{MongoDB, TreeDB};
use crate::host::merkle::{MerkleError, MerkleErrorCode, MerkleNode, MerkleProof, MerkleTree};
use crate::host::poseidon::MERKLE_HASHER;
use crate::host::poseidon::POSEIDON_HASHER;
use ff::PrimeField;
use halo2_proofs::pairing::bn256::Fr;
use lazy_static;
use mongodb::bson::doc;
use mongodb::bson::{spec::BinarySubtype, Bson};
use mongodb::options::DropCollectionOptions;
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};
use std::cell::RefCell;
use std::rc::Rc;

fn deserialize_u64_as_binary<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok({
            let c: [u8; 8] = bytes.bytes.try_into().unwrap();
            u64::from_le_bytes(c)
        }),
        Ok(..) => Err(Error::invalid_value(Unexpected::Enum, &"Bson::Binary")),
        Err(e) => Err(e),
    }
}

fn serialize_u64_as_binary<S>(value: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let binary = Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: value.to_le_bytes().to_vec(),
    });
    binary.serialize(serializer)
}

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

#[derive(Clone)]
pub struct MongoMerkle<const DEPTH: usize> {
    root_hash: [u8; 32],
    default_hash: Vec<[u8; 32]>,
    db: Rc<RefCell<dyn TreeDB>>,
}

pub fn drop_collection<T>(database: String, name: String) -> Result<(), mongodb::error::Error> {
    let collection = db::get_collection::<MerkleRecord>(database, name)?;
    let options = DropCollectionOptions::builder().build();
    collection.drop(options)
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
    pub fn get_record(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        let mut cache = MERKLE_CACHE.lock().unwrap();
        if let Some(record) = cache.get(&(index, *hash)) {
            Ok(record.clone())
        } else {
            let record = self.db.borrow().get_merkle_record(index, hash);
            if let Ok(value) = record.clone() {
                cache.push((index, *hash), value);
            };
            record
        }
    }

    /* We always insert new record as there might be uncommitted update to the merkle tree */
    pub fn update_record(&mut self, record: MerkleRecord) -> Result<(), mongodb::error::Error> {
        let exists: Result<Option<MerkleRecord>, mongodb::error::Error> =
            self.get_record(record.index, &record.hash);
        //println!("record is none: {:?}", exists.as_ref().unwrap().is_none());
        exists.map_or_else(
            |e: mongodb::error::Error| Err(e),
            |r: Option<MerkleRecord>| {
                r.map_or_else(
                    || {
                        //println!("Do update record to DB for index {:?}, hash: {:?}", record.index, record.hash);
                        let mut cache = MERKLE_CACHE.lock().unwrap();
                        cache.push((record.index, record.hash), Some(record.clone()));
                        self.db.borrow_mut().set_merkle_record(record)?;
                        Ok(())
                    },
                    |_| Ok(()),
                )
            },
        )
    }

    //the input records must be in one leaf path
    pub fn update_leaf_path_records(
        &mut self,
        records: &Vec<MerkleRecord>,
    ) -> Result<(), mongodb::error::Error> {
        // sort records by index to ensure the parent node is processed before its child nodes.
        let mut sort_records: Vec<MerkleRecord> = records.clone();
        sort_records.sort_by(|r1, r2| r1.index.cmp(&r2.index));

        let mut new_records: Vec<MerkleRecord> = vec![];
        let mut check = true;
        for record in sort_records {
            // figure out whether a parent node had been added or not,
            // to save the cache/db reading for its child nodes for optimizing.
            if check {
                match self.get_record(record.index, &record.hash) {
                    Ok(Some(_)) => {}
                    _ => {
                        check = false;
                        new_records.push(record);
                    }
                }
            } else {
                new_records.push(record);
            }
        }

        if new_records.len() > 0 {
            let mut cache = MERKLE_CACHE.lock().unwrap();
            for record in new_records.iter() {
                cache.push((record.index, record.hash), Some(record.clone()));
            }
            self.db.borrow_mut().set_merkle_records(&new_records)?;
        }
        Ok(())
    }

    pub fn generate_default_node(&self, index: u64) -> Result<MerkleRecord, MerkleError> {
        let height = (index + 1).ilog2();
        let default = self.get_default_hash(height as usize)?;
        let child_hash = if height == Self::height() as u32 {
            [0; 32]
        } else {
            self.get_default_hash((height + 1) as usize)?
        };

        Ok(MerkleRecord {
            index,
            hash: default,
            data: [0; 32],
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

    fn get_or_generate_node(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<(MerkleRecord, bool), MerkleError> {
        let mut exist = false;
        let node = self
            .get_record(index, hash)
            .expect("Unexpected DB Error")
            .map_or_else(
                || -> Result<MerkleRecord, MerkleError> {
                    Ok(self.check_generate_default_node(index, hash)?)
                },
                |x| -> Result<MerkleRecord, MerkleError> {
                    exist = true;
                    assert!(x.index == index);
                    Ok(x)
                },
            )?;
        Ok((node, exist))
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MerkleRecord {
    #[serde(serialize_with = "self::serialize_u64_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u64_as_binary")]
    pub index: u64,
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    pub hash: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    pub left: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    pub right: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    pub data: [u8; 32],
}

impl MerkleNode<[u8; 32]> for MerkleRecord {
    fn index(&self) -> u64 {
        self.index
    }
    fn hash(&self) -> [u8; 32] {
        self.hash
    }
    fn set(&mut self, data: &Vec<u8>) {
        let mut hasher = POSEIDON_HASHER.clone();
        self.data = data.clone().try_into().unwrap();
        let batchdata = data
            .chunks(16)
            .into_iter()
            .map(|x| {
                let mut v = x.clone().to_vec();
                v.extend_from_slice(&[0u8; 16]);
                let f = v.try_into().unwrap();
                Fr::from_repr(f).unwrap()
            })
            .collect::<Vec<Fr>>();
        let values: [Fr; 2] = batchdata.try_into().unwrap();
        hasher.update(&values);
        self.hash = hasher.squeeze().to_repr();
        //println!("update with values {:?}", values);
        //println!("update with new hash {:?}", self.hash);
    }
    fn right(&self) -> Option<[u8; 32]> {
        Some(self.right)
    }
    fn left(&self) -> Option<[u8; 32]> {
        Some(self.left)
    }
}

impl MerkleRecord {
    fn new(index: u64) -> Self {
        MerkleRecord {
            index,
            hash: [0; 32],
            data: [0; 32],
            left: [0; 32],
            right: [0; 32],
        }
    }

    pub fn data_as_u64(&self) -> [u64; 4] {
        [
            u64::from_le_bytes(self.data[0..8].try_into().unwrap()),
            u64::from_le_bytes(self.data[8..16].try_into().unwrap()),
            u64::from_le_bytes(self.data[16..24].try_into().unwrap()),
            u64::from_le_bytes(self.data[24..32].try_into().unwrap()),
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
    fn get_default_hash(&self, depth: usize) -> Result<[u8; 32], MerkleError> {
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
            default_hash: (*DEFAULT_HASH_VEC).clone(),
            db: db.unwrap_or_else(|| Rc::new(RefCell::new(MongoDB::new(addr)))),
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
            data: [0; 32],
            left: *left,
            right: *right,
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
            .map(|(index, hash, left, right)| MerkleRecord {
                index,
                data: [0; 32],
                left,
                right,
                hash,
            })
            .to_vec();

        records.push(leaf.clone());
        self.update_leaf_path_records(&records)
            .expect("Unexpected DB Error when update records.");

        Ok(())
    }

    fn get_node_with_hash(&self, index: u64, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        let (node, _) = self.get_or_generate_node(index, hash)?;
        Ok(node)
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
        let (mut acc_node, mut parent_exist) = self.get_or_generate_node(acc, &hash)?;
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
                if parent_exist {
                    (acc_node, parent_exist) = self.get_or_generate_node(acc, &hash)?
                } else {
                    acc_node = self.check_generate_default_node(acc, &hash)?
                }
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

#[cfg(test)]
mod tests {
    use super::db::get_collection;
    use super::{MerkleRecord, MongoMerkle, DEFAULT_HASH_VEC};
    use crate::host::db::{get_collection_name, MONGODB_DATABASE, MONGODB_DATA_NAME_PREFIX};
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::utils::{bytes_to_u64, field_to_bytes};
    use halo2_proofs::pairing::bn256::Fr;
    use mongodb::bson::doc;

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

        let mut mt =
            MongoMerkle::<DEPTH>::construct(TEST_ADDR, DEFAULT_HASH_VEC[DEPTH].clone(), None);
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection =
            get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);

        let (mut leaf, proof) = mt.get_leaf_with_proof(index).unwrap();
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
        let bytesdata = field_to_bytes(&data).to_vec();
        leaf.set(&bytesdata);
        let proof = mt.set_leaf_with_proof(&leaf).unwrap();
        assert_eq!(mt.verify_proof(&proof).unwrap(), true);
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

        // 1
        let mut mt =
            MongoMerkle::<DEPTH>::construct(TEST_ADDR, DEFAULT_HASH_VEC[DEPTH].clone(), None);
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection =
            get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);

        // 3
        let a = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(TEST_ADDR, a, None);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
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

        // 1
        let mut mt =
            MongoMerkle::<DEPTH>::construct(TEST_ADDR, DEFAULT_HASH_VEC[DEPTH].clone(), None);
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), TEST_ADDR);
        let collection =
            get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);

        // 3
        let a = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(TEST_ADDR, a, None);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
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

        // 1
        let mut mt = MongoMerkle::<DEPTH>::construct(test_addr, DEFAULT_HASH_VEC[DEPTH], None);
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), test_addr);
        let collection =
            get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);
        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();

        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);

        // 3
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        leaf.set(&LEAF2_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data, LEAF2_DATA);

        // 4
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        leaf.set(&LEAF3_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let (leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data, LEAF3_DATA);

        // 5
        let root = mt.get_root_hash();
        let mt = MongoMerkle::<DEPTH>::construct(test_addr, root, None);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
        assert!(mt.verify_proof(&proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data, LEAF2_DATA);
        assert!(mt.verify_proof(&proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data, LEAF3_DATA);
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
}
