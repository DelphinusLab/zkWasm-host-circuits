use halo2_proofs::pairing::bn256::Fq;
use futures::executor;
use poseidon::Poseidon;
use crate::host::merkle:: {
    MerkleError,
    MerkleTree,
    MerkleLeaf
};
use mongodb::{
    Client,
    bson::doc,
    results::{InsertOneResult, UpdateResult},
};
use mongodb::bson::{oid::ObjectId, spec::BinarySubtype, Bson};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};
use super::MONGODB_URI;

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

fn bytes_to_bson(x: [u8;32]) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: x.into(),
    })
}

struct MongoMerkle {
    contract_address: [u8;32]
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
        index: u32
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
        let mut filter = doc! {};
        filter.insert("index", index);
        collection.find_one(filter, None).await
    }

    pub async fn update_record(
        &self,
        record: MerkleRecord
    ) -> Result<(), mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
        let exist = collection.find_one(doc! { "index": record.index }, None).await?.map_or(false, |_| true);
        if exist {
            collection
                .update_one(
                    doc! { "index" : record.index },
                    doc! { "$set": {
                            "data": bytes_to_bson(record.data),
                            "hash": bytes_to_bson(record.hash),
                        }
                    },
                    None
                )
                .await?;
        } else {
            collection
                .insert_one(record, None)
                .await?;
        }
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
    data: [u8; 32],
}


impl MerkleLeaf<[u8;32]> for MerkleRecord {
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
}

impl MerkleRecord {
    fn new(index: u32) -> Self {
        MerkleRecord { index, hash: [0; 32], data: [0; 32] }
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
    fn default_hash(&self, depth: usize) -> [u8; 32] {
        let mut leaf_hash = Self::empty_leaf(0).hash;
        for _ in 0..(Self::height() - depth) {
            leaf_hash = self.hash(&leaf_hash, &leaf_hash);
        }
        leaf_hash
    }
}

impl MerkleTree<[u8;32], 20> for MongoMerkle {

    type Id = [u8; 32];
    type Leaf = MerkleRecord;

    fn construct(id: Self::Id) -> Self {
        MongoMerkle {
           contract_address: id
        }
    }

    fn hash(&self, a:&[u8;32], b:&[u8;32]) -> [u8; 32] {
        let mut hasher = gen_hasher();
        let a = Fq::from_bytes(a).unwrap();
        let b = Fq::from_bytes(b).unwrap();
        hasher.update(&[a,b]);
        hasher.squeeze().to_bytes()
    }

    fn get_hash(&self, index: u32) -> Result<[u8; 32], MerkleError> {
        self.boundary_check(index)?;
        let height = (index+1).ilog2();
        let v = executor::block_on(self.get_record(index)).expect("Unexpected DB Error");
        let hash = v.map_or(self.default_hash(height as usize), |x| x.hash);
        Ok(hash)
    }

    fn set_hash(&mut self, index: u32, hash: &[u8; 32]) -> Result<(), MerkleError> {
        self.boundary_check(index)?;
        let v = executor::block_on(self.get_record(index)).expect("Unexpected DB Error");
        let record = v.map_or(
            MerkleRecord {
                index,
                data:[0; 32],
                hash:*hash
            }, |x| {
                MerkleRecord {
                    index,
                    data: x.data,
                    hash:*hash,
                }
            });
        executor::block_on(self.update_record(record)).expect("Unexpected DB Error");
        Ok(())
    }

    fn get_leaf(&self, index: u32) -> Result<Self::Leaf, MerkleError> {
        self.leaf_check(index)?;
        let v = executor::block_on(self.get_record(index)).expect("Unexpected DB Error");
        let height = (index+1).ilog2();
        let leaf = v.map_or(
            MerkleRecord {
                index,
                hash: self.default_hash(height as usize),
                data:[0; 32],
            }, |x| {
                MerkleRecord {
                    index,
                    data: x.data,
                    hash:x.hash,
                }
            });
        Ok(leaf)
    }

    fn set_leaf(&mut self, leaf: &MerkleRecord) -> Result<(), MerkleError> {
        self.boundary_check(leaf.index())?;
        executor::block_on(self.update_record(leaf.clone())).expect("Unexpected DB Error");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::host::merkle::{MerkleLeaf, MerkleTree};
    use super::MongoMerkle;
    #[test]
    fn test_mongo_merkle_dummy() {
       let mut mt = MongoMerkle::construct([0;32]);
       let mut leaf = mt.get_leaf(2_u32.pow(20) - 1).unwrap();
       leaf.set(&[1u8;32].to_vec());
       mt.set_leaf(&leaf).unwrap();
       let leaf = mt.get_leaf(2_u32.pow(20) - 1).unwrap();
       println!("kv pair < {:?}, {:?} >", leaf.index, leaf.data);
    }
}
