use mongodb::{
    bson::doc,
    options::DropCollectionOptions,
    sync::{Client, Collection},
};

use crate::host::datahash::DataHashRecord;
use crate::host::mongomerkle::MerkleRecord;
use mongodb::bson::{spec::BinarySubtype, to_bson, Bson};
use mongodb::error::{Error, ErrorKind};
use mongodb::options::{InsertManyOptions, UpdateOptions};
use mongodb::results::InsertManyResult;
use mongodb::IndexModel;

pub const MONGODB_DATABASE: &str = "zkwasm-mongo-merkle";
pub const MONGODB_MERKLE_NAME_PREFIX: &str = "MERKLEDATA";
pub const MONGODB_DATA_NAME_PREFIX: &str = "DATAHASH";
const DUPLICATE_KEY_ERROR_CODE: i32 = 11000;

pub trait TreeDB {
    fn get_merkle_record(
        &self,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error>;

    fn get_database_client(&self) -> Result<&Client, mongodb::error::Error>;

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
    client: Client,
}

impl MongoDB {
    pub fn new(cname_id: [u8; 32], uri: Option<String>) -> Self {
        let uri = uri.map_or("mongodb://localhost:27017".to_string(), |x| x.clone());
        let client = Client::with_uri_str(uri).expect("Unexpected DB Error");
        Self { cname_id, client }
    }
}

impl MongoDB {
    pub fn get_collection<T>(
        &self,
        database: String,
        name: String,
    ) -> Result<Collection<T>, mongodb::error::Error> {
        let database = self.client.database(database.as_str());
        let collection = database.collection::<T>(name.as_str());
        Ok(collection)
    }

    pub fn drop_collection<T>(
        &self,
        database: String,
        name: String,
    ) -> Result<(), mongodb::error::Error> {
        let collection = self.get_collection::<MerkleRecord>(database, name)?;
        let options = DropCollectionOptions::builder().build();
        collection.drop(options)
    }

    pub fn merkel_collection(&self) -> Result<Collection<MerkleRecord>, mongodb::error::Error> {
        let cname = get_collection_name(MONGODB_MERKLE_NAME_PREFIX.to_string(), self.cname_id);
        let collection =
            self.get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname.to_string());
        let index = IndexModel::builder().keys(doc! { "hash": -1 }).build();
        let _ = collection.as_ref().unwrap().create_index(index, None);
        collection
    }

    pub fn data_collection(&self) -> Result<Collection<DataHashRecord>, mongodb::error::Error> {
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), self.cname_id);
        let collection =
            self.get_collection::<DataHashRecord>(MONGODB_DATABASE.to_string(), cname.to_string());
        let index = IndexModel::builder().keys(doc! { "hash": -1 }).build();
        let _ = collection.as_ref().unwrap().create_index(index, None);
        collection
    }
}

impl TreeDB for MongoDB {
    fn get_database_client(&self) -> Result<&Client, mongodb::error::Error> {
        Ok(&self.client)
    }
    fn get_merkle_record(
        &self,
        hash: &[u8; 32],
    ) -> Result<Option<MerkleRecord>, mongodb::error::Error> {
        let collection = self.merkel_collection()?;
        let mut filter = doc! {};
        filter.insert("hash", u256_to_bson(hash));
        collection.find_one(filter, None)
    }

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<(), mongodb::error::Error> {
        let options = UpdateOptions::builder().upsert(true).build();
        let mut filter = doc! {};
        filter.insert("hash", u256_to_bson(&record.hash));
        let record_doc = to_bson(&record).unwrap().as_document().unwrap().to_owned();
        let update = doc! {"$set": record_doc};
        let collection = self.merkel_collection()?;
        collection.update_one(filter, update, options)?;
        Ok(())
    }

    fn set_merkle_records(
        &mut self,
        records: &Vec<MerkleRecord>,
    ) -> Result<(), mongodb::error::Error> {
        let options = InsertManyOptions::builder().ordered(false).build();
        let collection = self.merkel_collection()?;
        let ret = collection.insert_many(records, options);
        if let Some(e) = filter_duplicate_key_error(ret) {
            return Err(e);
        }
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
        let options = UpdateOptions::builder().upsert(true).build();
        let mut filter = doc! {};
        filter.insert("hash", u256_to_bson(&record.hash));
        let record_doc = to_bson(&record).unwrap().as_document().unwrap().to_owned();
        let update = doc! {"$set": record_doc};
        let collection = self.data_collection()?;
        collection.update_one(filter, update, options)?;
        Ok(())
    }
}

pub fn filter_duplicate_key_error(
    result: mongodb::error::Result<InsertManyResult>,
) -> Option<Error> {
    match result {
        Ok(_) => None,
        Err(err) => {
            if let ErrorKind::BulkWrite(we) = err.kind.as_ref() {
                if let Some(write_errors) = &we.write_errors {
                    if write_errors
                        .iter()
                        .all(|we| we.code == DUPLICATE_KEY_ERROR_CODE)
                    {
                        return None;
                    }
                }
            }
            Some(err)
        }
    }
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

pub fn get_collection<T>(
    client: &Client,
    database: String,
    name: String,
) -> Result<Collection<T>, mongodb::error::Error> {
    let database = client.database(database.as_str());
    let collection = database.collection::<T>(name.as_str());
    Ok(collection)
}

pub fn get_collection_name(name_prefix: String, id: [u8; 32]) -> String {
    format!("{}_{}", name_prefix, hex::encode(id))
}
