use mongodb::bson::{spec::BinarySubtype, to_bson, Bson};
use mongodb::error::{Error, ErrorKind};
use mongodb::options::{InsertManyOptions, UpdateOptions};
use mongodb::results::InsertManyResult;
use mongodb::{
    bson::doc,
    options::DropCollectionOptions,
    sync::{Client, Collection},
};

use crate::host::datahash::DataHashRecord;
use crate::host::mongomerkle::MerkleRecord;
use anyhow::Result;
use rocksdb::{DB, Options, WriteBatch};
use std::path::Path;
use std::sync::Arc;

pub const MONGODB_DATABASE: &str = "zkwasm-mongo-merkle";
pub const MONGODB_MERKLE_NAME_PREFIX: &str = "MERKLEDATA";
pub const MONGODB_DATA_NAME_PREFIX: &str = "DATAHASH";
const DUPLICATE_KEY_ERROR_CODE: i32 = 11000;

pub trait TreeDB {
    fn get_merkle_record(&self, hash: &[u8; 32]) -> Result<Option<MerkleRecord>, anyhow::Error>;

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<(), anyhow::Error>;

    fn set_merkle_records(&mut self, records: &Vec<MerkleRecord>) -> Result<(), anyhow::Error>;

    fn get_data_record(&self, hash: &[u8; 32]) -> Result<Option<DataHashRecord>, anyhow::Error>;

    fn set_data_record(&mut self, record: DataHashRecord) -> Result<(), anyhow::Error>;
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

    pub fn get_database_client(&self) -> Result<&Client, mongodb::error::Error> {
        Ok(&self.client)
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
        self.get_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), cname.to_string())
    }

    pub fn data_collection(&self) -> Result<Collection<DataHashRecord>, mongodb::error::Error> {
        let cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), self.cname_id);
        self.get_collection::<DataHashRecord>(MONGODB_DATABASE.to_string(), cname.to_string())
    }
}

impl TreeDB for MongoDB {
    fn get_merkle_record(&self, hash: &[u8; 32]) -> Result<Option<MerkleRecord>, anyhow::Error> {
        let collection = self.merkel_collection()?;
        let mut filter = doc! {};
        filter.insert("_id", u256_to_bson(hash));
        let record = collection.find_one(filter, None)?;
        Ok(record)
    }

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<(), anyhow::Error> {
        let options = UpdateOptions::builder().upsert(true).build();
        let mut filter = doc! {};
        filter.insert("_id", u256_to_bson(&record.hash));
        let record_doc = to_bson(&record).unwrap().as_document().unwrap().to_owned();
        let update = doc! {"$set": record_doc};
        let collection = self.merkel_collection()?;
        collection.update_one(filter, update, options)?;
        Ok(())
    }

    fn set_merkle_records(&mut self, records: &Vec<MerkleRecord>) -> Result<(), anyhow::Error> {
        let options = InsertManyOptions::builder().ordered(false).build();
        let collection = self.merkel_collection()?;
        let ret = collection.insert_many(records, options);
        if let Some(e) = filter_duplicate_key_error(ret) {
            return Err(e.into());
        }
        Ok(())
    }

    fn get_data_record(&self, hash: &[u8; 32]) -> Result<Option<DataHashRecord>, anyhow::Error> {
        let collection = self.data_collection()?;
        let mut filter = doc! {};
        filter.insert("_id", u256_to_bson(hash));
        collection.find_one(filter, None).map_err(|e| e.into())
    }

    fn set_data_record(&mut self, record: DataHashRecord) -> Result<(), anyhow::Error> {
        let options = UpdateOptions::builder().upsert(true).build();
        let mut filter = doc! {};
        filter.insert("_id", u256_to_bson(&record.hash));
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


pub struct RocksDB {
    db: Arc<DB>,
    merkle_cf_name: String,
    data_cf_name: String,
    read_only: bool,
}

impl Clone for RocksDB {
    fn clone(&self) -> Self {
        RocksDB {
            db: Arc::clone(&self.db),
            merkle_cf_name: self.merkle_cf_name.clone(),
            data_cf_name: self.data_cf_name.clone(),
            read_only: self.read_only,
        }
    }
}

impl RocksDB {
    // create  RocksDB
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let merkle_cf_name = "merkle_records";
        let data_cf_name = "data_records";

        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);

        let cfs = vec![merkle_cf_name, data_cf_name];
        let db = DB::open_cf(&opts, path, cfs)?;

        Ok(Self {
            db: Arc::new(db),
            merkle_cf_name: merkle_cf_name.to_string(),
            data_cf_name: data_cf_name.to_string(),
            read_only : false,
        })
    }

    // 清空数据库
    pub fn clear(&self) -> Result<()> {
        if self.read_only {
            return Err(anyhow::anyhow!(
                "Read only mode db call clear."
            ));
        }

        // clear merkle records
        let merkle_cf = self.db.cf_handle(&self.merkle_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;

        let iter = self.db.iterator_cf(merkle_cf, rocksdb::IteratorMode::Start);
        let mut batch = WriteBatch::default();

        for item in iter {
            let (key, _) = item?;
            batch.delete_cf(merkle_cf, &key);
        }

        // clear data records
        let data_cf = self.db.cf_handle(&self.data_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;

        let iter = self.db.iterator_cf(data_cf, rocksdb::IteratorMode::Start);

        for item in iter {
            let (key, _) = item?;
            batch.delete_cf(data_cf, &key);
        }

        self.db.write(batch)?;
        Ok(())
    }

    pub fn new_read_only<P: AsRef<Path>>(path: P) -> Result<Self> {
        let merkle_cf_name = "merkle_records";
        let data_cf_name = "data_records";

        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.create_missing_column_families(true);

        let cfs = vec![merkle_cf_name, data_cf_name];
        let db = DB::open_cf_for_read_only(&opts, path, cfs, false)?;

        Ok(Self {
            db: Arc::new(db),
            merkle_cf_name: merkle_cf_name.to_string(),
            data_cf_name: data_cf_name.to_string(),
            read_only: true,
        })
    }

    fn validate_merkle_record_set_for_read_only(&self, record: &MerkleRecord) -> Result<()> {
        if self
            .get_merkle_record(&record.hash)?
            .map_or(true, |it| it != *record)
        {
            Err(anyhow::anyhow!(
                "Read only mode! Merkle record does not match, record {:?} should already be set",
                record.hash
            ))
        } else {
            Ok(())
        }
    }

    fn validate_data_record_set_for_read_only(&self, record: &DataHashRecord) -> Result<()> {
        if self
            .get_data_record(&record.hash)?
            .map_or(true, |it| it != *record)
        {
            Err(anyhow::anyhow!(
                "Read only mode! Data record does not match, record {:?} should already be set",
                record.hash
            ))
        } else {
            Ok(())
        }
    }
}

impl TreeDB for RocksDB {
    fn get_merkle_record(&self, hash: &[u8; 32]) -> Result<Option<MerkleRecord>> {
        let cf = self.db.cf_handle(&self.merkle_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;

        match self.db.get_cf(cf, hash)? {
            Some(data) => {
                let record = MerkleRecord::from_slice(&data)?;
                Ok(Some(record))
            },
            None => Ok(None),
        }
    }

    fn set_merkle_record(&mut self, record: MerkleRecord) -> Result<()> {
        if self.read_only {
            self.validate_merkle_record_set_for_read_only(&record)?;
            return Ok(());
        }

        let cf = self.db.cf_handle(&self.merkle_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;

        let serialized = record.to_slice();
        self.db.put_cf(cf, &record.hash, serialized)?;
        Ok(())
    }

    fn set_merkle_records(&mut self, records: &Vec<MerkleRecord>) -> Result<()> {
        let cf = self.db.cf_handle(&self.merkle_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;

        if self.read_only {
            for record in records {
                self.validate_merkle_record_set_for_read_only(record)?;
            }
            return Ok(());
        }

        let mut batch = WriteBatch::default();
        for record in records {
            let serialized = record.to_slice();
            batch.put_cf(cf, &record.hash, serialized);
        }
        self.db.write(batch)?;
        Ok(())
    }

    fn get_data_record(&self, hash: &[u8; 32]) -> Result<Option<DataHashRecord>> {
        let cf = self.db.cf_handle(&self.data_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;

        match self.db.get_cf(cf, hash)? {
            Some(data) => {
                let record = DataHashRecord::from_slice(&data)?;
                Ok(Some(record))
            },
            None => Ok(None),
        }
    }

    fn set_data_record(&mut self, record: DataHashRecord) -> Result<()> {
        if self.read_only {
            self.validate_data_record_set_for_read_only(&record)?;
            return Ok(());
        }

        let cf = self.db.cf_handle(&self.data_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;

        let serialized = record.to_slice();
        self.db.put_cf(cf, &record.hash, serialized)?;
        Ok(())
    }
}
