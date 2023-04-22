use futures::executor;
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
    //TODO: use config for db uri if we want
    let client = Client::with_uri_str("mongodburi").await?;
    let database = client.database(database.as_str());
    Ok(database.collection::<T>(name.as_str()))
}

impl MongoMerkle {
    fn get_collection_name(&self) -> String {
        return "abc".to_string();
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
    ) -> Result<UpdateResult, mongodb::error::Error> {
        let dbname = Self::get_db_name();
        let cname = self.get_collection_name();
        let collection = get_collection::<MerkleRecord>(dbname, cname).await?;
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
            .await
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
}

fn default_hash(depth: u32) -> [u8; 32] {
    [0; 32]
}

impl MerkleTree<[u8;32], 20> for MongoMerkle {

    type Id = [u8; 32];
    type Leaf = MerkleRecord;

    fn construct(id: Self::Id) -> Self {
        MongoMerkle {
           contract_address: id
        }
    }

    fn hash(&self, a:[u8;32], b:[u8;32]) -> [u8; 32] {
        todo!()
    }

    fn get_hash(&self, index: u32) -> Result<[u8; 32], MerkleError> {
        self.boundary_check(index)?;
        let height = (index+1).ilog2();
        let v = executor::block_on(self.get_record(index)).expect("Unexpected DB Error");
        let hash = v.map_or(default_hash(height), |x| x.hash);
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
                hash: default_hash(height),
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

