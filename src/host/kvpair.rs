use super::MONGODB_URI;
use crate::host::merkle::{MerkleError, MerkleErrorCode, MerkleNode, MerkleTree};
use crate::host::poseidon::gen_hasher;
use futures::executor;
use halo2_proofs::pairing::bn256::Fq;
use lazy_static;
use mongodb::bson::{spec::BinarySubtype, Bson};
use mongodb::options::DropCollectionOptions;
use mongodb::{bson::doc, Client};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};

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

fn bytes_to_bson(x: &[u8; 32]) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: (*x).into(),
    })
}

#[derive(Debug)]
pub struct MongoMerkle {
    contract_address: [u8; 32],
    root_hash: [u8; 32],
    default_hash: Vec<[u8; 32]>,
}

pub async fn get_collection<T>(
    database: String,
    name: String,
) -> Result<mongodb::Collection<T>, mongodb::error::Error> {
    let client = Client::with_uri_str(MONGODB_URI).await?;
    let database = client.database(database.as_str());
    Ok(database.collection::<T>(name.as_str()))
}

pub async fn drop_collection<T>(
    database: String,
    name: String,
) -> Result<(), mongodb::error::Error> {
    let collection = get_collection::<MerkleRecord>(database, name).await?;
    let options = DropCollectionOptions::builder().build();
    collection.drop(options).await
}

impl MongoMerkle {
    fn get_collection_name(&self) -> String {
        format!("MERKLEDATA_{}", hex::encode(&self.contract_address))
    }
    fn get_db_name() -> String {
        return "zkwasmkvpair".to_string();
    }

    pub async fn get_record(
        &self,
        index: u32,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
        let mut filter = doc! {};
        filter.insert("index", index);
        filter.insert("hash", bytes_to_bson(hash));
        collection.find_one(filter, None).await
    }

    /* We always insert new record as there might be uncommitted update to the merkle tree */
    pub async fn update_record(&self, record: MerkleRecord) -> Result<(), mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
        let mut filter = doc! {};
        filter.insert("index", record.index);
        filter.insert("hash", bytes_to_bson(&record.hash));
        let exists = collection.find_one(filter, None).await?;
        exists.map_or(
            {
                collection.insert_one(record, None).await?;
                Ok(())
            },
            |_| {
                //println!("find existing node, preventing duplicate");
                Ok(())
            },
        )
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MerkleRecord {
    index: u32,
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    hash: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    left: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    right: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_as_binary")]
    data: [u8; 32],
}

impl MerkleNode<[u8; 32]> for MerkleRecord {
    fn index(&self) -> u32 {
        self.index
    }
    fn hash(&self) -> [u8; 32] {
        self.hash
    }
    fn set(&mut self, data: &Vec<u8>) {
        let mut hasher = gen_hasher();
        self.data = data.clone().try_into().unwrap();
        let batchdata = data
            .chunks(16)
            .into_iter()
            .map(|x| {
                let mut v = x.clone().to_vec();
                v.extend_from_slice(&[0u8; 16]);
                let f = v.try_into().unwrap();
                Fq::from_bytes(&f).unwrap()
            })
            .collect::<Vec<Fq>>();
        let values: [Fq; 2] = batchdata.try_into().unwrap();
        hasher.update(&values);
        self.hash = hasher.squeeze().to_bytes();
    }
    fn right(&self) -> Option<[u8; 32]> {
        Some(self.right)
    }
    fn left(&self) -> Option<[u8; 32]> {
        Some(self.left)
    }
}

impl MerkleRecord {
    fn new(index: u32) -> Self {
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

impl MongoMerkle {
    pub fn height() -> usize {
        return 20;
    }
    fn empty_leaf(index: u32) -> MerkleRecord {
        let mut leaf = MerkleRecord::new(index);
        leaf.set(&[0; 32].to_vec());
        leaf
    }
    /// depth start from 0 upto Self::height()
    fn get_default_hash(&self, depth: usize) -> Result<[u8; 32], MerkleError> {
        if depth <= Self::height() {
            Ok(self.default_hash[Self::height() - depth])
        } else {
            Err(MerkleError::new(
                [0; 32],
                depth as u32,
                MerkleErrorCode::InvalidDepth,
            ))
        }
    }
}

lazy_static::lazy_static! {
    static ref DEFAULT_HASH_VEC: Vec<[u8; 32]> = {
        let mut leaf_hash = MongoMerkle::empty_leaf(0).hash;
        let mut default_hash = vec![leaf_hash];
        for _ in 0..(MongoMerkle::height()) {
            leaf_hash = MongoMerkle::hash(&leaf_hash, &leaf_hash);
            default_hash.push(leaf_hash);
        }
        default_hash
    };
}

impl MerkleTree<[u8; 32], 20> for MongoMerkle {
    type Id = [u8; 32];
    type Addr = [u8; 32];
    type Node = MerkleRecord;

    fn construct(addr: Self::Addr, id: Self::Id) -> Self {
        MongoMerkle {
            contract_address: addr,
            root_hash: id,
            default_hash: (*DEFAULT_HASH_VEC).clone(),
        }
    }

    fn get_root_hash(&self) -> [u8; 32] {
        self.root_hash
    }

    fn update_root_hash(&mut self, hash: &[u8; 32]) {
        self.root_hash = hash.clone();
    }

    fn hash(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
        let mut hasher = gen_hasher();
        let a = Fq::from_bytes(a).unwrap();
        let b = Fq::from_bytes(b).unwrap();
        hasher.update(&[a, b]);
        hasher.squeeze().to_bytes()
    }

    fn set_parent(
        &mut self,
        index: u32,
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
        executor::block_on(self.update_record(record)).expect("Unexpected DB Error");
        Ok(())
    }

    fn get_node_with_hash(&self, index: u32, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        let v = executor::block_on(self.get_record(index, hash)).expect("Unexpected DB Error");
        //println!("get_node_with_hash {} {:?} {:?}", index, hash, v);
        let height = (index + 1).ilog2();
        v.map_or(
            {
                let default = self.get_default_hash(height as usize)?;
                let child_hash = if height == Self::height() as u32 {
                    [0; 32]
                } else {
                    self.get_default_hash((height + 1) as usize)?
                };
                if default == *hash {
                    Ok(MerkleRecord {
                        index,
                        hash: self.get_default_hash(height as usize)?,
                        data: [0; 32],
                        left: child_hash,
                        right: child_hash,
                    })
                } else {
                    Err(MerkleError::new(*hash, index, MerkleErrorCode::InvalidHash))
                }
            },
            |x| {
                assert!(x.index == index);
                Ok(x)
            },
        )
    }

    fn set_leaf(&mut self, leaf: &MerkleRecord) -> Result<(), MerkleError> {
        self.boundary_check(leaf.index())?; //should be leaf check?
        executor::block_on(self.update_record(leaf.clone())).expect("Unexpected DB Error");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{MerkleRecord, MongoMerkle, DEFAULT_HASH_VEC};
    use crate::host::{
        kvpair::drop_collection,
        merkle::{MerkleNode, MerkleTree},
    };
    use futures::executor;

    #[test]
    /* Test for check parent node
     * 1. Clear m tree collection. Create default empty m tree. Check root.
     * 2. Update index=2_u32.pow(20) - 1 (first leaf) leave value.
     * 3. Update index=2_u32.pow(20) (second leaf) leave value.
     * 4. Get index=2_u32.pow(19) - 1 node with hash and confirm the left and right are previous set leaves.
     * 5. Load mt from DB and Get index=2_u32.pow(19) - 1 node with hash and confirm the left and right are previous set leaves.
     */
    fn test_mongo_merkle_parent_node() {
        // Init checking results
        const TEST_ADDR: [u8; 32] = [1; 32];

        const DEFAULT_ROOT_HASH: [u8; 32] = [
            166, 157, 178, 62, 35, 83, 140, 56, 9, 235, 134, 184, 20, 145, 63, 43, 245, 186, 75,
            233, 43, 42, 187, 217, 104, 152, 219, 89, 125, 199, 161, 9,
        ];
        const DEFAULT_ROOT_HASH64: [u64; 4] = [
            4074723173704310182,
            3116368985344895753,
            15689180094961269493,
            694055158784170088,
        ];

        const INDEX1: u32 = 2_u32.pow(20) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF1: [u8; 32] = [
            146, 154, 4, 1, 65, 7, 114, 67, 209, 68, 222, 153, 65, 139, 137, 45, 124, 86, 61, 115,
            142, 90, 166, 41, 22, 133, 154, 149, 141, 76, 198, 11,
        ];
        const ROOT64_HASH_AFTER_LEAF1: [u64; 4] = [
            4859954923657534098,
            3281306917386732753,
            3001185769554269820,
            848449750789948694,
        ];

        const INDEX2: u32 = 2_u32.pow(20);
        const LEAF2_DATA: [u8; 32] = [
            0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF2: [u8; 32] = [
            85, 8, 43, 221, 140, 128, 115, 118, 70, 71, 130, 25, 120, 183, 70, 207, 168, 71, 44,
            41, 135, 151, 172, 193, 83, 125, 3, 205, 166, 227, 251, 20,
        ];
        const ROOT64_HASH_AFTER_LEAF2: [u64; 4] = [
            8535307061291583573,
            14935826940672755526,
            13955695952081471400,
            1512052405456567635,
        ];

        const PARENT_INDEX: u32 = 2_u32.pow(19) - 1;

        // 1
        let mut mt = MongoMerkle::construct(TEST_ADDR, DEFAULT_HASH_VEC[MongoMerkle::height()]);
        executor::block_on(drop_collection::<MerkleRecord>(
            MongoMerkle::get_db_name(),
            mt.get_collection_name(),
        ))
        .expect("Unexpected DB Error");
        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, DEFAULT_ROOT_HASH);
        assert_eq!(root64, DEFAULT_ROOT_HASH64);

        // 2
        let (mut leaf1, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf1.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf1).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF1);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF1);

        // 3
        let (mut leaf2, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        leaf2.set(&LEAF2_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf2).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF2);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF2);

        // 4
        let parent_hash: [u8; 32] = MongoMerkle::hash(&leaf1.hash, &leaf2.hash);
        let parent_node = mt.get_node_with_hash(PARENT_INDEX, &parent_hash).unwrap();
        assert_eq!(leaf1.hash, parent_node.left().unwrap());
        assert_eq!(leaf2.hash, parent_node.right().unwrap());

        // 5
        let a: [u8; 32] = ROOT_HASH_AFTER_LEAF2;
        let mt_loaded: MongoMerkle = MongoMerkle::construct(TEST_ADDR, a);
        assert_eq!(mt_loaded.get_root_hash(), a);
        let (leaf1, _) = mt_loaded.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf1.index, INDEX1);
        assert_eq!(leaf1.data, LEAF1_DATA);
        let (leaf2, _) = mt_loaded.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf2.index, INDEX2);
        assert_eq!(leaf2.data, LEAF2_DATA);
        let parent_hash: [u8; 32] = MongoMerkle::hash(&leaf1.hash, &leaf2.hash);
        let parent_node = mt_loaded
            .get_node_with_hash(PARENT_INDEX, &parent_hash)
            .unwrap();
        assert_eq!(leaf1.hash, parent_node.left().unwrap());
        assert_eq!(leaf2.hash, parent_node.right().unwrap());
    }

    #[test]
    /* Basic tests for 20 height m tree
     * 1. Clear m tree collection. Create default empty m tree. Check root.
     * 2. Update index=2_u32.pow(20) - 1 (first leaf) leave value. Check root.
     * 3. Check index=2_u32.pow(20) - 1 leave value updated.
     * 4. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_single_leaf_update() {
        // Init checking results
        const DEFAULT_ROOT_HASH: [u8; 32] = [
            166, 157, 178, 62, 35, 83, 140, 56, 9, 235, 134, 184, 20, 145, 63, 43, 245, 186, 75,
            233, 43, 42, 187, 217, 104, 152, 219, 89, 125, 199, 161, 9,
        ];
        const DEFAULT_ROOT_HASH64: [u64; 4] = [
            4074723173704310182,
            3116368985344895753,
            15689180094961269493,
            694055158784170088,
        ];

        const INDEX1: u32 = 2_u32.pow(20) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF1: [u8; 32] = [
            146, 154, 4, 1, 65, 7, 114, 67, 209, 68, 222, 153, 65, 139, 137, 45, 124, 86, 61, 115,
            142, 90, 166, 41, 22, 133, 154, 149, 141, 76, 198, 11,
        ];
        const ROOT64_HASH_AFTER_LEAF1: [u64; 4] = [
            4859954923657534098,
            3281306917386732753,
            3001185769554269820,
            848449750789948694,
        ];

        // 1
        let mut mt = MongoMerkle::construct([0; 32], DEFAULT_HASH_VEC[MongoMerkle::height()]);
        executor::block_on(drop_collection::<MerkleRecord>(
            MongoMerkle::get_db_name(),
            mt.get_collection_name(),
        ))
        .expect("Unexpected DB Error");
        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, DEFAULT_ROOT_HASH);
        assert_eq!(root64, DEFAULT_ROOT_HASH64);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF1);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF1);

        // 3
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);

        // 4
        let a = ROOT_HASH_AFTER_LEAF1;
        let mt = MongoMerkle::construct([0; 32], a);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
    }

    #[test]
    /* Tests for 20 height m tree with updating multple leaves
     * 1. Clear m tree collection. Create default empty m tree. Check root (default one, A).
     * 2. Update index=2_u32.pow(20) - 1 (first leaf) leave value. Check root (1 leave updated, B). Check index=2_u32.pow(20) - 1 leave value updated.
     * 3. Update index=2_u32.pow(20) (second leaf) leave value. Check root (1 leave updated, C). Check index=2_u32.pow(20) leave value updated.
     * 4. Update index=2_u32.pow(21) - 2 (last leaf) leave value. Check root (1 leave updated, D). Check index=2_u32.pow(21) -2 leave value updated.
     * 5. Load m tree from DB with D root hash, check root and leaves' values.
     */
    fn test_mongo_merkle_multi_leaves_update() {
        // Init checking results
        const DEFAULT_ROOT_HASH: [u8; 32] = [
            166, 157, 178, 62, 35, 83, 140, 56, 9, 235, 134, 184, 20, 145, 63, 43, 245, 186, 75,
            233, 43, 42, 187, 217, 104, 152, 219, 89, 125, 199, 161, 9,
        ];
        const DEFAULT_ROOT_HASH64: [u64; 4] = [
            4074723173704310182,
            3116368985344895753,
            15689180094961269493,
            694055158784170088,
        ];

        const INDEX1: u32 = 2_u32.pow(20) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF1: [u8; 32] = [
            146, 154, 4, 1, 65, 7, 114, 67, 209, 68, 222, 153, 65, 139, 137, 45, 124, 86, 61, 115,
            142, 90, 166, 41, 22, 133, 154, 149, 141, 76, 198, 11,
        ];
        const ROOT64_HASH_AFTER_LEAF1: [u64; 4] = [
            4859954923657534098,
            3281306917386732753,
            3001185769554269820,
            848449750789948694,
        ];

        const INDEX2: u32 = 2_u32.pow(20);
        const LEAF2_DATA: [u8; 32] = [
            0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF2: [u8; 32] = [
            85, 8, 43, 221, 140, 128, 115, 118, 70, 71, 130, 25, 120, 183, 70, 207, 168, 71, 44,
            41, 135, 151, 172, 193, 83, 125, 3, 205, 166, 227, 251, 20,
        ];
        const ROOT64_HASH_AFTER_LEAF2: [u64; 4] = [
            8535307061291583573,
            14935826940672755526,
            13955695952081471400,
            1512052405456567635,
        ];

        const INDEX3: u32 = 2_u32.pow(21) - 2;
        const LEAF3_DATA: [u8; 32] = [
            18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const ROOT_HASH_AFTER_LEAF3: [u8; 32] = [
            28, 84, 99, 220, 229, 74, 35, 103, 22, 167, 191, 145, 179, 136, 24, 147, 189, 87, 94,
            132, 23, 141, 77, 57, 81, 181, 165, 158, 112, 90, 186, 34,
        ];
        const ROOT64_HASH_AFTER_LEAF3: [u64; 4] = [
            7431866161196913692,
            10599372027842242326,
            4129111565513152445,
            2502411982702228817,
        ];

        // 1
        let mut mt = MongoMerkle::construct([0; 32], DEFAULT_HASH_VEC[MongoMerkle::height()]);
        executor::block_on(drop_collection::<MerkleRecord>(
            MongoMerkle::get_db_name(),
            mt.get_collection_name(),
        ))
        .expect("Unexpected DB Error");
        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, DEFAULT_ROOT_HASH);
        assert_eq!(root64, DEFAULT_ROOT_HASH64);

        // 2
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        leaf.set(&LEAF1_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF1);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF1);

        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);

        // 3
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        leaf.set(&LEAF2_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF2);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF2);

        let (leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data, LEAF2_DATA);

        // 4
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        leaf.set(&LEAF3_DATA.to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();

        let root = mt.get_root_hash();
        let root64 = root
            .chunks(8)
            .into_iter()
            .map(|x| u64::from_le_bytes(x.to_vec().try_into().unwrap()))
            .collect::<Vec<u64>>();
        assert_eq!(root, ROOT_HASH_AFTER_LEAF3);
        assert_eq!(root64, ROOT64_HASH_AFTER_LEAF3);

        let (leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data, LEAF3_DATA);

        // 5
        let mt = MongoMerkle::construct([0; 32], ROOT_HASH_AFTER_LEAF3);
        assert_eq!(mt.get_root_hash(), ROOT_HASH_AFTER_LEAF3);
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
        let (leaf, _) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data, LEAF2_DATA);
        let (leaf, _) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data, LEAF3_DATA);
    }

    #[test]
    fn test_generate_kv_input() {
        let mut mt = MongoMerkle::construct([0; 32], DEFAULT_HASH_VEC[MongoMerkle::height()]);
        let (mut leaf, _) = mt.get_leaf_with_proof(2_u32.pow(20) - 1).unwrap();
        leaf.set(&[1u8; 32].to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();
        let root = mt.get_root_hash();

        // get {
        //     current_root: 4*64 --> bn254    // fr 2^256-C
        //     index: 1*64
        //     ret: 4:64     ---> 2 * bn254
        // }
        // set {
        //     current_root: 4*64
        //     index: 1*64
        //     data: 4:64
        // }
        todo!()
    }
}
