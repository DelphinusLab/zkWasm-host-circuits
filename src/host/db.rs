use mongodb::{
    bson::doc,
    sync::{Client, Collection},
};

use crate::host::datahash::DataHashRecord;
use crate::host::mongomerkle::MerkleRecord;
use mongodb::bson::{spec::BinarySubtype, Bson};

const MONGODB_URI: &str = "mongodb://localhost:27017";
pub const MONGODB_DATABASE: &str = "zkwasm-mongo-merkle";
pub const MONGODB_MERKLE_NAME_PREFIX: &str = "MERKLEDATA";
pub const MONGODB_DATA_NAME_PREFIX: &str = "DATAHASH";

lazy_static::lazy_static! {
    pub static ref CLIENT: Client= {
        let mongo_uri = std::env::var("ZKWASM_MONGO").unwrap_or(String::from(MONGODB_URI));
        Client::with_uri_str(&mongo_uri).expect("Unexpected DB Error")
    };
}

pub trait TreeDB {
    fn get_merkle_record(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error>;

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<(), mongodb::error::Error>;

    fn set_merkle_records(
        &mut self,
        records: &Vec<MerkleRecord>,
    ) -> Result<(), mongodb::error::Error>;

    fn get_data_record(
        &self,
        hash: &[u8; 32],
    ) -> Result<Option<DataHashRecord>, mongodb::error::Error>;

    fn set_data_record(&mut self, record: DataHashRecord) -> Result<(), mongodb::error::Error>;
}

#[derive(Clone)]
pub struct MongoDB {
    cname_id: [u8; 32],
}

impl MongoDB {
    pub fn new(cname_id: [u8; 32]) -> Self {
        Self { cname_id }
    }
}

impl MongoDB {
    pub fn merkel_collection(&self) -> Result<Collection<MerkleRecord>, mongodb::error::Error> {
        let cname = get_collection_name(MONGODB_MERKLE_NAME_PREFIX.to_string(), self.cname_id);
        get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname.to_string())
    }

    pub fn data_collection(&self) -> Result<Collection<DataHashRecord>, mongodb::error::Error> {
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), self.cname_id);
        get_collection::<DataHashRecord>(MONGODB_DATABASE.to_string(), cname.to_string())
    }
}

impl TreeDB for MongoDB {
    fn get_merkle_record(
        &self,
        index: u64,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        let collection = self.merkel_collection()?;
        let mut filter = doc! {};
        filter.insert("index", u64_to_bson(index));
        filter.insert("hash", u256_to_bson(hash));
        collection.find_one(filter, None)
    }

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<(), mongodb::error::Error> {
        let collection = self.merkel_collection()?;
        collection.insert_one(record, None)?;
        Ok(())
    }

    fn set_merkle_records(
        &mut self,
        records: &Vec<MerkleRecord>,
    ) -> Result<(), mongodb::error::Error> {
        let collection = self.merkel_collection()?;
        collection.insert_many(records, None)?;
        Ok(())
    }

    fn get_data_record(
        &self,
        hash: &[u8; 32],
    ) -> Result<Option<DataHashRecord>, mongodb::error::Error> {
        let collection = self.data_collection()?;
        let mut filter = doc! {};
        filter.insert("hash", u256_to_bson(hash));
        collection.find_one(filter, None)
    }

    fn set_data_record(&mut self, record: DataHashRecord) -> Result<(), mongodb::error::Error> {
        let collection = self.data_collection()?;
        collection.insert_one(record, None)?;
        Ok(())
    }
}

pub fn get_collection<T>(
    database: String,
    name: String,
) -> Result<Collection<T>, mongodb::error::Error> {
    let database = CLIENT.database(database.as_str());
    let collection = database.collection::<T>(name.as_str());
    Ok(collection)
}

pub fn u256_to_bson(x: &[u8; 32]) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: (*x).into(),
    })
}

pub fn u64_to_bson(x: u64) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: x.to_le_bytes().to_vec(),
    })
}

pub fn get_collection_name(name_prefix: String, id: [u8; 32]) -> String {
    format!("{}_{}", name_prefix, hex::encode(id))
}
