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

    fn start_record(&mut self, record_db: RocksDB) -> Result<()>;

    fn stop_record(&mut self) -> Result<RocksDB>;

    fn is_recording(&self) -> bool;
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

    fn start_record(&mut self, _record_db: RocksDB) -> Result<()> {
        Err(anyhow::anyhow!("MongoDB does not support record"))
    }

    fn stop_record(&mut self) -> Result<RocksDB> {
        Err(anyhow::anyhow!("MongoDB does not support record"))
    }

    fn is_recording(&self) -> bool {
        false
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
    record_db: Option<Box<RocksDB>>,
}

impl Clone for RocksDB {
    fn clone(&self) -> Self {
        RocksDB {
            db: Arc::clone(&self.db),
            merkle_cf_name: self.merkle_cf_name.clone(),
            data_cf_name: self.data_cf_name.clone(),
            read_only: self.read_only,
            record_db: self.record_db.clone(),
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
            record_db: None,
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
            record_db: None,
        })
    }

    fn validate_merkle_record_set_for_read_only(&self, record: &MerkleRecord) -> Result<()> {
        if self
            .get_merkle_record(&record.hash)?
            .map_or(true, |it| {
                if it != *record {
                    println!("found record: {:?}", it);
                    println!("provided record: {:?}", record);
                } 
                
                it.hash != record.hash
            })
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

        match self.db.get_cf(cf, hash.clone())? {
            Some(data) => {
                let record = MerkleRecord::from_slice(&data)?;
                if self.record_db.is_some() {
                    let record_db = self.record_db.clone().unwrap();
                    let cf = record_db.db.cf_handle(&self.merkle_cf_name)
                        .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;
                    record_db.db.put_cf(cf, hash, data)?;
                }
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
        self.db.put_cf(cf, &record.hash, serialized.clone())?;
        if self.record_db.is_some() {
            let record_db = self.record_db.clone().unwrap();
            let cf = record_db.db.cf_handle(&record_db.merkle_cf_name)
                .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;
            record_db.db.put_cf(cf, record.hash, serialized)?;
        }
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
        if !self.record_db.is_some() {
            let mut batch = WriteBatch::default();
            for record in records {
                let serialized = record.to_slice();
                batch.put_cf(cf, &record.hash, serialized);
            }
            self.db.write(batch)?;
        } else {
            let record_db = self.record_db.clone().unwrap();
            let record_db_cf = record_db.db.cf_handle(&record_db.merkle_cf_name)
                .ok_or_else(|| anyhow::anyhow!("Merkle column family not found"))?;
            let mut batch = WriteBatch::default();
            let mut record_db_batch = WriteBatch::default();
            for record in records {
                let serialized = record.to_slice();
                batch.put_cf(cf, &record.hash, serialized.clone());
                record_db_batch.put_cf(record_db_cf, &record.hash, serialized);
            }
            self.db.write(batch)?;
            record_db.db.write(record_db_batch)?;
        }
        Ok(())
    }

    fn get_data_record(&self, hash: &[u8; 32]) -> Result<Option<DataHashRecord>> {
        let cf = self.db.cf_handle(&self.data_cf_name)
            .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;

        match self.db.get_cf(cf, hash)? {
            Some(data) => {
                let record = DataHashRecord::from_slice(&data)?;
                if self.record_db.is_some() {
                    let record_db = self.record_db.clone().unwrap();
                    let cf = record_db.db.cf_handle(&record_db.data_cf_name)
                        .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;
                    record_db.db.put_cf(cf, &record.hash, data)?;
                }
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
        self.db.put_cf(cf, &record.hash, serialized.clone())?;
        if self.record_db.is_some() {
            let record_db = self.record_db.clone().unwrap();
            let cf = record_db.db.cf_handle(&record_db.data_cf_name)
                .ok_or_else(|| anyhow::anyhow!("Data column family not found"))?;
            record_db.db.put_cf(cf, &record.hash, serialized)?;
        }
        Ok(())
    }

    fn start_record(&mut self, record_db: RocksDB) -> Result<()> {
        if self.record_db.is_some() {
            return Err(anyhow::anyhow!("Record already started"));
        }
        self.record_db = Some(Box::new(record_db));
        Ok(())
    }

    fn stop_record(&mut self) -> Result<RocksDB> {
        if self.record_db.is_none() {
            return Err(anyhow::anyhow!("Record not started"));
        }
        let record_db = self.record_db.clone().unwrap();
        self.record_db = None;
        Ok(*record_db)
    }

    fn is_recording(&self) -> bool {
        self.record_db.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use crate::host::datahash::DataHashRecord;
    use crate::host::mongomerkle::MerkleRecord;

    #[test]
    fn test_rocksdb_record_functionality() -> Result<()> {
        // Create temporary directories for the databases
        let main_dir = tempdir()?;
        let record_dir = tempdir()?;

        let main_path = main_dir.path().to_path_buf();
        let record_path = record_dir.path().to_path_buf();

        // Create the main and record databases
        let mut db = RocksDB::new(&main_path)?;
        let record_db = RocksDB::new(&record_path)?;

        // Create test data
        let key1 = [1u8; 32]; // Merkle record key
        let key2 = [2u8; 32]; // Data record key
        let key3 = [3u8; 32]; // New Merkle record key
        let key4 = [4u8; 32]; // Merkle records batch key
        let key5 = [5u8; 32]; // New Data record key

        let left1 = [10u8; 32];
        let right1 = [11u8; 32];
        

        let merkle_record1 = MerkleRecord {
            index: 0,
            hash: key1,
            left: Some(left1),
            right: Some(right1),
            data: Some([20u8; 32]),
        };

        let data_record1 = DataHashRecord {
            hash: key2,
            data: vec![20, 21, 22],
        };

        let left2 = [30u8; 32];
        let right2 = [31u8; 32];

        let merkle_record2 = MerkleRecord {
            index: 0,
            hash: key3,
            left: Some(left2),
            right: Some(right2),
            data: Some([21u8; 32]),
        };

        let left3 = [40u8; 32];
        let right3 = [41u8; 32];

        let merkle_record3 = MerkleRecord {
            index: 0,
            hash: key4,
            left: Some(left3),
            right: Some(right3),
            data: Some([22u8; 32]),
        };

        // Also test a record with None values
        let merkle_record_none = MerkleRecord {
            index: 0,
            hash: [42u8; 32],
            left: None,
            right: None,
            data: None,
        };

        let data_record2 = DataHashRecord {
            hash: key5,
            data: vec![50, 51, 52],
        };

        // Insert initial records into main db
        db.set_merkle_record(merkle_record1.clone())?;
        db.set_data_record(data_record1.clone())?;

        // Start recording
        db.start_record(record_db.clone())?;

        // Verify recording is active
        assert!(db.is_recording(), "Recording should be active");

        // Test 1: Get existing merkle record and verify it's recorded
        let retrieved_merkle = db.get_merkle_record(&key1)?;
        assert!(retrieved_merkle.is_some(), "Should retrieve merkle record");
        assert_eq!(retrieved_merkle.unwrap(), merkle_record1, "Retrieved merkle record should match original");

        // Verify record was stored in record_db
        let record_db_clone = record_db.clone();
        let record_merkle = record_db_clone.get_merkle_record(&key1)?;
        assert!(record_merkle.is_some(), "Record DB should have the retrieved merkle record");
        assert_eq!(record_merkle.unwrap(), merkle_record1, "Record DB merkle record should match original");

        // Test 2: Set new merkle record and verify it's recorded
        db.set_merkle_record(merkle_record2.clone())?;

        // Verify record was stored in record_db
        let record_db_clone = record_db.clone();
        let record_merkle2 = record_db_clone.get_merkle_record(&key3)?;
        assert!(record_merkle2.is_some(), "Record DB should have the new merkle record");
        assert_eq!(record_merkle2.unwrap(), merkle_record2, "Record DB new merkle record should match");

        // Test record with None values
        db.set_merkle_record(merkle_record_none.clone())?;
        let record_db_clone = record_db.clone();
        let record_merkle_none = record_db_clone.get_merkle_record(&merkle_record_none.hash)?;
        assert!(record_merkle_none.is_some(), "Record DB should have the None-valued merkle record");
        assert_eq!(record_merkle_none.unwrap(), merkle_record_none, "Record DB None-valued merkle record should match");

        // Test 3: Set merkle records batch and verify they're recorded
        let batch_records = vec![merkle_record3.clone()];
        db.set_merkle_records(&batch_records)?;

        // Verify batch record was stored in record_db
        let record_db_clone = record_db.clone();
        let record_merkle3 = record_db_clone.get_merkle_record(&key4)?;
        assert!(record_merkle3.is_some(), "Record DB should have the batch merkle record");
        assert_eq!(record_merkle3.unwrap(), merkle_record3, "Record DB batch merkle record should match");

        // Test 4: Get existing data record and verify it's recorded
        let retrieved_data = db.get_data_record(&key2)?;
        assert!(retrieved_data.is_some(), "Should retrieve data record");
        assert_eq!(retrieved_data.unwrap(), data_record1, "Retrieved data record should match original");

        // Verify record was stored in record_db
        let record_db_clone = record_db.clone();
        let record_data = record_db_clone.get_data_record(&key2)?;
        assert!(record_data.is_some(), "Record DB should have the retrieved data record");
        assert_eq!(record_data.unwrap(), data_record1, "Record DB data record should match original");

        // Test 5: Set new data record and verify it's recorded
        db.set_data_record(data_record2.clone())?;

        // Verify record was stored in record_db
        let record_db_clone = record_db.clone();
        let record_data2 = record_db_clone.get_data_record(&key5)?;
        assert!(record_data2.is_some(), "Record DB should have the new data record");
        assert_eq!(record_data2.unwrap(), data_record2, "Record DB new data record should match");

        // Stop recording and verify
        let _stopped_record_db = db.stop_record()?;
        assert!(!db.is_recording(), "Recording should be inactive after stopping");

        // Clean up
        main_dir.close()?;
        record_dir.close()?;

        Ok(())
    }
}

