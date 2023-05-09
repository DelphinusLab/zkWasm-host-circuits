use halo2_proofs::pairing::bn256::Fq;
use futures::executor;
use poseidon::Poseidon;
use crate::host::merkle:: {
    MerkleError,
    MerkleTree,
    MerkleNode,
    MerkleErrorCode,
};
use mongodb::{
    Client,
    bson::doc
};
use mongodb::bson::{
    spec::BinarySubtype, Bson
};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};
use super::MONGODB_URI;
use lazy_static;

/* Poseidon hash settings */
const T: usize = 9;
const RATE: usize = 8;
const R_F: usize = 8;
const R_P: usize = 63;

fn gen_hasher() -> Poseidon<Fq, T, RATE> {
   Poseidon::<Fq, T, RATE>::new(R_F, R_P)
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

fn bytes_to_bson(x: &[u8;32]) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: (*x).into(),
    })
}

pub struct MongoMerkle {
    contract_address: [u8;32],
    root_hash: [u8; 32],
    default_hash: Vec<[u8; 32]>
}

pub async fn get_collection<T>(
    database: String,
    name: String,
) -> Result<mongodb::Collection<T>, mongodb::error::Error> {
    let client = Client::with_uri_str(MONGODB_URI).await?;
    let database = client.database(database.as_str());
    Ok(database.collection::<T>(name.as_str()))
}

impl MongoMerkle {
    fn get_collection_name(&self) -> String {
        format!("MERKLEDATA-{}", hex::encode(&self.contract_address))
    }
    fn get_db_name() -> String {
        return "zkwasmkvpair".to_string()
    }

    pub async fn get_record (
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
    pub async fn update_record(
        &self,
        record: MerkleRecord
    ) -> Result<(), mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
        collection
            .insert_one(record, None)
            .await?;
        Ok(())
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


impl MerkleNode<[u8;32]> for MerkleRecord {
    fn index(&self) -> u32 { self.index }
    fn hash(&self) -> [u8;32] { self.hash }
    fn set(&mut self, data: &Vec<u8>) {
        let mut hasher = gen_hasher();
        self.data = data.clone().try_into().unwrap();
        let batchdata = data.chunks(16).into_iter().map(|x| {
            let mut v = x.clone().to_vec();
            v.extend_from_slice(&[0u8;16]);
            let f = v.try_into().unwrap();
            Fq::from_bytes(&f).unwrap()
        }).collect::<Vec<Fq>>();
        let values:[Fq; 2] = batchdata.try_into().unwrap();
        hasher.update(&values);
        self.hash = hasher.squeeze().to_bytes();
    }
    fn right(&self) -> Option<[u8; 32]> { Some(self.right) }
    fn left(&self) -> Option<[u8; 32]> { Some(self.left) }
}

impl MerkleRecord {
    fn new(index: u32) -> Self {
        MerkleRecord { index, hash: [0; 32], data: [0; 32], left:[0;32], right: [0;32] }
    }

    pub fn data_as_u64(&self) -> [u64; 4]  {
        [
            u64::from_le_bytes(self.data[0..8].try_into().unwrap()),
            u64::from_le_bytes(self.data[8..16].try_into().unwrap()),
            u64::from_le_bytes(self.data[16..24].try_into().unwrap()),
            u64::from_le_bytes(self.data[24..32].try_into().unwrap()),
        ]
    }
}

impl MongoMerkle {
    fn height() -> usize {
        return 20
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
            Err(MerkleError::new([0;32], depth as u32, MerkleErrorCode::InvalidDepth))
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

impl MerkleTree<[u8;32], 20> for MongoMerkle {

    type Id = [u8; 32];
    type Node = MerkleRecord;

    fn construct(id: Self::Id, hash: Option<[u8; 32]>) -> Self {
        MongoMerkle {
           contract_address: id,
           root_hash: hash.map_or(DEFAULT_HASH_VEC[Self::height()], |x| x),
           default_hash: (*DEFAULT_HASH_VEC).clone()
        }
    }


    fn get_root_hash(&self) -> [u8; 32] {
        self.root_hash
    }

    fn update_root_hash(&mut self, hash: &[u8; 32]) {
        self.root_hash = hash.clone();
    }

    fn hash(a:&[u8;32], b:&[u8;32]) -> [u8; 32] {
        let mut hasher = gen_hasher();
        let a = Fq::from_bytes(a).unwrap();
        let b = Fq::from_bytes(b).unwrap();
        hasher.update(&[a,b]);
        hasher.squeeze().to_bytes()
    }

    fn set_parent_hash(&mut self, index: u32, hash: &[u8; 32], left: &[u8;32], right: &[u8; 32]) -> Result<(), MerkleError> {
        self.boundary_check(index)?;
        let record = MerkleRecord {
                index,
                data:[0; 32],
                left: *left,
                right: *right,
                hash: *hash
            };
        //println!("set_node_with_hash {} {:?}", index, hash);
        executor::block_on(self.update_record(record)).expect("Unexpected DB Error");
        Ok(())
    }

    fn get_node_with_hash(&self, index: u32, hash: &[u8; 32]) -> Result<Self::Node, MerkleError> {
        let v = executor::block_on(self.get_record(index, hash))
            .expect("Unexpected DB Error");
        //println!("get_node_with_hash {} {:?} {:?}", index, hash, v);
        let height = (index+1).ilog2();
        v.map_or(
            {
                let default = self.get_default_hash(height as usize)?;
                let child_hash = if height == Self::height() as u32 {
                    [0; 32]
                } else {
                    self.get_default_hash((height+1) as usize)?
                };
                if default == *hash {
                    Ok(MerkleRecord {
                        index,
                        hash: self.get_default_hash(height as usize)?,
                        data:[0; 32],
                        left: child_hash,
                        right: child_hash,
                    })
                } else {
                    Err (MerkleError::new(*hash, index, MerkleErrorCode::InvalidHash))
                }
            }, |x| {
                assert!(x.index == index);
                Ok(x)
            }
        )
    }

    fn set_leaf(&mut self, leaf: &MerkleRecord) -> Result<(), MerkleError> {
        self.boundary_check(leaf.index())?;
        executor::block_on(self.update_record(leaf.clone())).expect("Unexpected DB Error");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::host::merkle::{MerkleNode, MerkleTree};
    use super::MongoMerkle;
    #[test]
    fn test_mongo_merkle_dummy() {
        let mut mt = MongoMerkle::construct([0;32], None);
        let root = mt.get_root_hash();
        println!("root hash is {:?}", root);
        let err = mt.get_leaf_with_proof(2_u32.pow(20) - 1);
        println!("err is {:?}", err);
        let (mut leaf, _) = mt.get_leaf_with_proof(2_u32.pow(20) - 1).unwrap();
        leaf.set(&[1u8;32].to_vec());
        mt.set_leaf_with_proof(&leaf).unwrap();
        let (leaf, _) = mt.get_leaf_with_proof(2_u32.pow(20) - 1).unwrap();
        println!("kv pair < {:?}, {:?} >", leaf.index, leaf.data);
    }

    #[test]
    fn test_generate_kv_input() {
        let mut mt = MongoMerkle::construct([0;32], None);
        let (mut leaf, _) = mt.get_leaf_with_proof(2_u32.pow(20) - 1).unwrap();
        leaf.set(&[1u8;32].to_vec());
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
