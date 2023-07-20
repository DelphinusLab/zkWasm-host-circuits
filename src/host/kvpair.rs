use super::MONGODB_URI;
use crate::host::merkle::{MerkleError, MerkleErrorCode, MerkleNode, MerkleTree};
use crate::host::poseidon::MERKLE_HASHER;
use crate::host::poseidon::POSEIDON_HASHER;
use ff::PrimeField;
use halo2_proofs::pairing::bn256::Fr;
use lazy_static;
use mongodb::bson::{spec::BinarySubtype, Bson};
use mongodb::options::DropCollectionOptions;
//use mongodb::options::InsertManyOptions;
use mongodb::{
    bson::doc,
    sync::{Client, Collection},
};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::host::cache::MERKLE_CACHE;


const CACHE: bool = false;

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
pub struct MongoMerkle<const DEPTH: usize> {
    client: Client,
    contract_address: [u8; 32],
    root_hash: [u8; 32],
    default_hash: Vec<[u8; 32]>,
}

pub fn get_collection<T>(
    client: &Client,
    database: String,
    name: String,
) -> Result<Collection<T>, mongodb::error::Error> {
    let database = client.database(database.as_str());
    let collection = database.collection::<T>(name.as_str());
    Ok(collection)
}

pub fn drop_collection<T>(
    client: &Client,
    database: String,
    name: String,
) -> Result<(), mongodb::error::Error> {
    let collection = get_collection::<MerkleRecord>(client, database, name)?;
    let options = DropCollectionOptions::builder().build();
    collection.drop(options)
}

impl<const DEPTH: usize> MongoMerkle<DEPTH> {
    fn get_collection_name(&self) -> String {
        format!("MERKLEDATA_{}", hex::encode(&self.contract_address))
    }
    fn get_db_name() -> String {
        return "zkwasmkvpair".to_string();
    }

    pub fn get_record(
        &self,
        index: u32,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        if CACHE {
            let mut cache: std::sync::MutexGuard<'_, std::collections::BTreeMap<(u32, [u8; 32]), Option<MerkleRecord>>> = MERKLE_CACHE.lock().unwrap();
            //println!("Try cache get {:?}, {:?}", index, hash.clone());
            let cache_record = cache.get(&(index, hash.clone()));
            //println!("cache_record is some: {:?}", cache_record.is_some());
            let mut cache_miss: bool = false;
            let r = cache_record.map_or_else(|| {
                //println!("cache miss get from DB: {}", index);
                let dbname = Self::get_db_name();
                let cname = self.get_collection_name();
                let collection = get_collection::<MerkleRecord>(&self.client, dbname, cname).ok()?;
                let mut filter = doc! {};
                filter.insert("index", index);
                filter.insert("hash", bytes_to_bson(hash));
                cache_miss = true;
                collection.find_one(filter, None).ok()?
            }, |x| x.clone());

            if cache_miss == true {
                //println!("cache insert: {:?}, {:?}", index, hash.clone());
                cache.insert((index, hash.clone()), r.clone());
            }
            Ok(r)
        } else {
            let dbname = Self::get_db_name();
            let cname = self.get_collection_name();
            let collection = get_collection::<MerkleRecord>(&self.client, dbname, cname)?;
            let mut filter = doc! {};
            filter.insert("index", index);
            filter.insert("hash", bytes_to_bson(hash));
            collection.find_one(filter, None)
        }
    }

    // or: [{and: [index=??? hash=???]}, {and: [index=??? hash= }

    pub fn get_records(
        &self,
        index: &Vec<MerkleRecord>
    ) -> Result<(Vec<MerkleRecord>, Vec<MerkleRecord>), mongodb::error::Error> {
        println!("get records with size {}", index.len());
        let mut docs:Vec<mongodb::bson::Document>= vec![];
        for record in index.iter() {
            let mut and_doc:Vec<mongodb::bson::Document>= vec![];
            and_doc.push(doc!{"index": record.index});
            and_doc.push(doc!{"hash": bytes_to_bson(&record.hash)});
            docs.push(doc!{"$and": and_doc});
        }
        let filter = doc! {
            "$or": docs
        };
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(&self.client, dbname, cname)?;
        let mut cursor = collection.find(filter, None)?;
        let mut find = vec![];
        let mut notfind = index.clone();

        while let Some(record) = cursor.next() {
            let r = record.unwrap();
            println!("find {:?}", r.index);
            find.push(r.clone());
            notfind.remove(notfind.iter().position(|x| {x.clone() == r.clone()}).unwrap());
        }
        Ok((find, notfind))
    }

    /* We always insert new record as there might be uncommitted update to the merkle tree */
    pub fn update_records(&self, record: Vec<MerkleRecord>) -> Result<(), mongodb::error::Error> {
        if CACHE {
            for record in record.iter() {
                MERKLE_CACHE.lock().unwrap().insert((record.index, record.hash), Some(record.clone()));
            }
            /*let dbname = Self::get_db_name();
            let cname = self.get_collection_name();
            let collection = get_collection::<MerkleRecord>(&self.client, dbname, cname)?;
            let mut filter = doc! {};
            filter.insert("index", record.index);
            filter.insert("hash", bytes_to_bson(&record.hash));
            let exists = collection.find_one(filter, None)?;
            exists.map_or(
                {
                    collection.insert_one(record, None)?;
                    Ok(())
                },
                |_| {
                    //println!("find existing node, preventing duplicate");
                    Ok(())
                },
            )*/
            Ok(())
        } else {
            //println!("cache miss update");
            let dbname = Self::get_db_name();
            let cname = self.get_collection_name();
            let collection = get_collection::<MerkleRecord>(&self.client, dbname, cname)?;
            /*
            collection.insert_many(record.clone(),
                Some(InsertManyOptions::builder().ordered(Some(true)).build()))?;
            */
            use ark_std::{end_timer, start_timer};
            let get_records_timer = start_timer!(|| "testing get records");
            let (_, upserts) = self.get_records(&record)?;
            println!("inserts : {}", upserts.len());
            if !upserts.is_empty() {
            }
            collection.insert_many(upserts, None)?;
            end_timer!(get_records_timer);
            Ok(())
        }
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


impl PartialEq for MerkleRecord {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.hash == other.hash
    }
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl MerkleNode<[u8; 32]> for MerkleRecord {
    fn index(&self) -> u32 {
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

impl<const DEPTH: usize> MongoMerkle<DEPTH> {
    pub fn height() -> usize {
        return DEPTH;
    }
    fn empty_leaf(index: u32) -> MerkleRecord {
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
                depth as u32,
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

    fn construct(addr: Self::Id, root: Self::Root) -> Self {
        let client = Client::with_uri_str(MONGODB_URI).expect("Unexpected DB Error");
        MongoMerkle {
            client,
            contract_address: addr,
            root_hash: root,
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
        let mut hasher = MERKLE_HASHER.clone();
        let a = Fr::from_repr(*a).unwrap();
        let b = Fr::from_repr(*b).unwrap();
        hasher.update_exact(&[a, b]).to_repr()
    }

    fn set_leaf_and_parents(&mut self, leaf: &MerkleRecord, parents: [(u32, [u8; 32], [u8; 32], [u8; 32]); DEPTH]) -> Result<(), MerkleError> {
        self.boundary_check(leaf.index())?; //should be leaf check?
        let mut records = parents.map(|(index, hash, left, right)| {
            MerkleRecord {
                index,
                data: [0; 32],
                left,
                right,
                hash,
            }
        }).to_vec();

        records.push(leaf.clone());

        self.update_records(records)
            .expect("Unexpected DB Error");
        Ok(())
    }


    fn get_node_with_hash(&self, index: u32, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        //use ark_std::{end_timer, start_timer};
        //let timer2 = start_timer!(|| "testing get_node_with_hash");
       //let timer = start_timer!(|| "testing get_record read");
        let v = self.get_record(index, hash).expect("Unexpected DB Error");
        //end_timer!(timer);
        //println!("get_node_with_hash {} {:?} {:?}", index, hash, v);
        let height = (index + 1).ilog2();
        v.map_or_else(
            || {
                //let timer3 = start_timer!(|| "Get get_default_hash");
                let default = self.get_default_hash(height as usize)?;
                //end_timer!(timer3);
                //let timer5 = start_timer!(|| "Get child_hash");
                let child_hash = if height == Self::height() as u32 {
                    [0; 32]
                } else {
                    self.get_default_hash((height + 1) as usize)?
                };
                //end_timer!(timer5);
                //let timer4 = start_timer!(|| "After get_default_hash");
                if default == *hash {
                    //end_timer!(timer4);
                    //end_timer!(timer2);
                    Ok(MerkleRecord {
                        index,
                        hash: self.get_default_hash(height as usize)?,
                        data: [0; 32],
                        left: child_hash,
                        right: child_hash,
                    })
                } else {
                    //end_timer!(timer4);
                    //end_timer!(timer2);
                    Err(MerkleError::new(*hash, index, MerkleErrorCode::InvalidHash))
                }
            },
            |x| {
                assert!(x.index == index);
                //end_timer!(timer4);
                //end_timer!(timer2);
                Ok(x)
            },
        )
    }

}

#[cfg(test)]
mod tests {
    use super::{MerkleRecord, MongoMerkle, DEFAULT_HASH_VEC, get_collection};
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use crate::utils::field_to_bytes;
    use halo2_proofs::pairing::bn256::Fr;
    use mongodb::bson::doc;

    #[test]
    /* Test for check parent node
     * 1. Clear m tree collection. Create default empty m tree. Check root.
     * 2. Update index=2_u32.pow(20) - 1 (first leaf) leave value.
     * 3. Update index=2_u32.pow(20) (second leaf) leave value.
     * 4. Get index=2_u32.pow(19) - 1 node with hash and confirm the left and right are previous set leaves.
     * 5. Load mt from DB and Get index=2_u32.pow(19) - 1 node with hash and confirm the left and right are previous set leaves.
     */
    fn test_mongo_merkle_parent_node() {
        const TEST_ADDR: [u8; 32] = [1; 32];
        let index = 2_u64.pow(20) - 1;
        let data = Fr::from(0x1000 as u64);

        let mut mt = MongoMerkle::<20>::construct(TEST_ADDR, DEFAULT_HASH_VEC[20].clone());
        let dbname: String =MongoMerkle::<20>::get_db_name();
        let cname = mt.get_collection_name();
        let collection = get_collection::<MerkleRecord>(&mt.client, dbname, cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);

        let (mut leaf, proof) = mt.get_leaf_with_proof(index as u32).unwrap();
        assert_eq!(mt.verify_proof(proof).unwrap(), true);
        let bytesdata = field_to_bytes(&data).to_vec();
        leaf.set(&bytesdata);
        let proof = mt.set_leaf_with_proof(&leaf).unwrap();
        assert_eq!(mt.verify_proof(proof).unwrap(), true);
    }

    #[test]
    /* Basic tests for 20 height m tree
     * 1. Update index=2_u32.pow(20) - 1 (first leaf) leave value. Check root.
     * 2. Check index=2_u32.pow(20) - 1 leave value updated.
     * 3. Load m tree from DB, check root and leave value.
     */
    fn test_mongo_merkle_single_leaf_update() {
        // Init checking results
        const TEST_ADDR: [u8; 32] = [2; 32];
        const INDEX1: u32 = 2_u32.pow(20) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        // 1
        let mut mt = MongoMerkle::<20>::construct(TEST_ADDR, DEFAULT_HASH_VEC[20].clone());
        let dbname: String =MongoMerkle::<20>::get_db_name();
        let cname = mt.get_collection_name();
        let collection = get_collection::<MerkleRecord>(&mt.client, dbname, cname).unwrap();
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
        let mut mt = MongoMerkle::<20>::construct(TEST_ADDR, a);
        assert_eq!(mt.get_root_hash(), a);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
        assert_eq!(mt.verify_proof(proof).unwrap(), true);
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
        use ark_std::{end_timer, start_timer};
        let timer = start_timer!(|| "testing multi leaves update");
        const TEST_ADDR: [u8; 32] = [3; 32];
        const INDEX1: u32 = 2_u32.pow(20) - 1;
        const LEAF1_DATA: [u8; 32] = [
            0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const INDEX2: u32 = 2_u32.pow(20);
        const LEAF2_DATA: [u8; 32] = [
            0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        const INDEX3: u32 = 2_u32.pow(21) - 2;
        const LEAF3_DATA: [u8; 32] = [
            18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];

        // 1
        let timer1 = start_timer!(|| "testing 1");
        let mut mt = MongoMerkle::<20>::construct(TEST_ADDR, DEFAULT_HASH_VEC[20]);
        let dbname: String =MongoMerkle::<20>::get_db_name();
        let cname = mt.get_collection_name();
        let collection = get_collection::<MerkleRecord>(&mt.client, dbname, cname).unwrap();
        let _ = collection.delete_many(doc! {}, None);
        end_timer!(timer1);

        // 2
        let timer2 = start_timer!(|| "Testing step 2");
        let timer_get = start_timer!(|| "Testing 1st get_leaf_with_proof");
        let (mut leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        end_timer!(timer_get);
        let timer_set = start_timer!(|| "Testing set node");
        leaf.set(&LEAF1_DATA.to_vec());
        end_timer!(timer_set);
        let timer_set_leaf = start_timer!(|| "Testing set_leaf_with_proof");
        mt.set_leaf_with_proof(&leaf).unwrap();
        end_timer!(timer_set_leaf);

        let timer_get2 = start_timer!(|| "Testing 2nd get_leaf_with_proof");
        let (leaf, _) = mt.get_leaf_with_proof(INDEX1).unwrap();
        end_timer!(timer_get2);
        end_timer!(timer2);
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);


        // 3
        let timer34 = start_timer!(|| "testing 3,4");
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
        end_timer!(timer34);


        // 5
        let timer5 = start_timer!(|| "testing 5");
        let root = mt.get_root_hash();
        let mut mt = MongoMerkle::<20>::construct(TEST_ADDR, root);
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX1).unwrap();
        assert_eq!(leaf.index, INDEX1);
        assert_eq!(leaf.data, LEAF1_DATA);
        assert!(mt.verify_proof(proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX2).unwrap();
        assert_eq!(leaf.index, INDEX2);
        assert_eq!(leaf.data, LEAF2_DATA);
        assert!(mt.verify_proof(proof).unwrap());
        let (leaf, proof) = mt.get_leaf_with_proof(INDEX3).unwrap();
        assert_eq!(leaf.index, INDEX3);
        assert_eq!(leaf.data, LEAF3_DATA);
        assert!(mt.verify_proof(proof).unwrap());
        end_timer!(timer5);
        end_timer!(timer);
    }

    #[test]
    fn test_mongo_merkle_cache() {
        for _ in 0..200 {
            test_mongo_merkle_multi_leaves_update();
        }
    }
}
