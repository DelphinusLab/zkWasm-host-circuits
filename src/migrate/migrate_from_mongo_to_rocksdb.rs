use anyhow::Result;
use clap::{App, Arg};
use mongodb::bson::doc;
use zkwasm_host_circuits::host::db::{MongoDB, RocksDB, TreeDB};

pub fn main() -> Result<()> {
    let matches = App::new("MongoDB to RocksDB Migration Tool")
        .version("1.0")
        .author("cuiweixe")
        .about("Migrates data from MongoDB to RocksDB")
        .arg(
            Arg::with_name("mongo-uri")
                .long("mongo-uri")
                .value_name("URI")
                .help("MongoDB connection URI")
                .default_value("mongodb://localhost:27017")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("rocks-db-path")
                .long("rocks-db-path")
                .value_name("PATH")
                .help("Path to RocksDB database")
                .default_value("./test_db")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("collection-id")
                .long("collection-id")
                .value_name("HEX")
                .help("Collection ID as 32-byte hex string (default: 32 bytes of 0x01)")
                .default_value(&"01".repeat(32))
                .takes_value(true),
        )
        .get_matches();

    let mongo_uri = matches.value_of("mongo-uri").unwrap();
    let rocks_db_path = matches.value_of("rocks-db-path").unwrap();
    let collection_id_hex = matches.value_of("collection-id").unwrap();

    // Parse collection ID from hex string
    let collection_id = parse_collection_id(collection_id_hex)?;

    migrate_from_mongo_to_rocksdb(mongo_uri, rocks_db_path, collection_id)?;

    Ok(())
}

fn parse_collection_id(hex_str: &str) -> Result<[u8; 32]> {
    // Remove "0x" prefix if present
    let hex_str = if hex_str.starts_with("0x") {
        &hex_str[2..]
    } else {
        hex_str
    };

    // Check if the string has the correct length
    if hex_str.len() != 64 {
        return Err(anyhow::anyhow!("Collection ID must be 32 bytes (64 hex characters)"));
    }

    // Parse hex string to bytes
    let bytes = hex::decode(hex_str)
        .map_err(|e| anyhow::anyhow!("Failed to parse collection ID: {}", e))?;

    // Convert to fixed-size array
    let mut result = [0u8; 32];
    result.copy_from_slice(&bytes);

    Ok(result)
}
pub fn migrate_from_mongo_to_rocksdb(mongo_uri: &str, rocks_db_path: &str, cname_id: [u8; 32]) -> Result<()> {
    println!("Starting migration from MongoDB to RocksDB");
    println!("MongoDB URI: {}", mongo_uri);
    println!("RocksDB path: {}", rocks_db_path);

    // Initialize MongoDB client
    let mongo_db = MongoDB::new(cname_id, Some(mongo_uri.to_string()));

    // Initialize RocksDB
    let mut rocks_db = RocksDB::new(rocks_db_path, None)?;

    // Clear RocksDB to ensure clean migration
    rocks_db.clear()?;

    // Migrate Merkle records
    let merkle_collection = mongo_db.merkel_collection()?;
    let merkle_cursor = merkle_collection.find(doc! {}, None)?;

    let mut merkle_count = 0;
    for result in merkle_cursor {
        match result {
            Ok(record) => {
                rocks_db.set_merkle_record(record)?;
                merkle_count += 1;
                if merkle_count % 1000 == 0 {
                    println!("Migrated {} Merkle records", merkle_count);
                }
            },
            Err(e) => println!("Error reading Merkle record: {}", e),
        }
    }

    // Migrate Data records
    let data_collection = mongo_db.data_collection()?;
    let data_cursor = data_collection.find(doc! {}, None)?;

    let mut data_count = 0;
    for result in data_cursor {
        match result {
            Ok(record) => {
                rocks_db.set_data_record(record)?;
                data_count += 1;
                if data_count % 1000 == 0 {
                    println!("Migrated {} Data records", data_count);
                }
            },
            Err(e) => println!("Error reading Data record: {}", e),
        }
    }

    println!("Migration complete!");
    println!("Total Merkle records migrated: {}", merkle_count);
    println!("Total Data records migrated: {}", data_count);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use zkwasm_host_circuits::host::datahash::DataHashRecord;
    use zkwasm_host_circuits::host::mongomerkle::MerkleRecord;
    use zkwasm_host_circuits::host::db::{MongoDB, RocksDB, TreeDB, MONGODB_DATABASE, MONGODB_MERKLE_NAME_PREFIX, MONGODB_DATA_NAME_PREFIX, get_collection_name};
    use tempfile::tempdir;

    #[test]
    fn test_migration() -> Result<()> {
        // Create a temporary directory for RocksDB
        let temp_dir = tempdir()?;
        let rocks_path = temp_dir.path().to_str().unwrap();

        // Use a test collection ID
        let test_id = [1u8; 32];

        // Setup MongoDB with test data
        let mongo_uri = "mongodb://localhost:27017";
        let mut mongo_db = MongoDB::new(test_id, Some(mongo_uri.to_string()));

        // Create test Merkle records
        let merkle_record1 = MerkleRecord {
            index: 0,
            hash: [1u8; 32],
            left: Some([2u8; 32]),
            right: Some([3u8; 32]),
            data: None,
        };

        let merkle_record2 = MerkleRecord {
            index: 0,
            hash: [4u8; 32],
            left: Some([5u8; 32]),
            right: Some([6u8; 32]),
            data: None,
        };

        // Create test Data records
        let data_record1 = DataHashRecord {
            hash: [7u8; 32],
            data: vec![1, 2, 3, 4],
        };

        let data_record2 = DataHashRecord {
            hash: [8u8; 32],
            data: vec![5, 6, 7, 8],
        };

        // Insert test data into MongoDB
        mongo_db.set_merkle_record(merkle_record1.clone())?;
        mongo_db.set_merkle_record(merkle_record2.clone())?;
        mongo_db.set_data_record(data_record1.clone())?;
        mongo_db.set_data_record(data_record2.clone())?;

        // Run migration
        migrate_from_mongo_to_rocksdb(mongo_uri, rocks_path, test_id)?;

        // Verify data in RocksDB
        let rocks_db = RocksDB::new(rocks_path)?;

        // Check Merkle records
        let retrieved_merkle1 = rocks_db.get_merkle_record(&merkle_record1.hash)?;
        let retrieved_merkle2 = rocks_db.get_merkle_record(&merkle_record2.hash)?;

        assert!(retrieved_merkle1.is_some());
        assert!(retrieved_merkle2.is_some());

        let retrieved_merkle1 = retrieved_merkle1.unwrap();
        let retrieved_merkle2 = retrieved_merkle2.unwrap();

        assert_eq!(retrieved_merkle1.hash, merkle_record1.hash);
        assert_eq!(retrieved_merkle1.left, merkle_record1.left);
        assert_eq!(retrieved_merkle1.right, merkle_record1.right);

        assert_eq!(retrieved_merkle2.hash, merkle_record2.hash);
        assert_eq!(retrieved_merkle2.left, merkle_record2.left);
        assert_eq!(retrieved_merkle2.right, merkle_record2.right);

        // Check Data records
        let retrieved_data1 = rocks_db.get_data_record(&data_record1.hash)?;
        let retrieved_data2 = rocks_db.get_data_record(&data_record2.hash)?;

        assert!(retrieved_data1.is_some());
        assert!(retrieved_data2.is_some());

        let retrieved_data1 = retrieved_data1.unwrap();
        let retrieved_data2 = retrieved_data2.unwrap();

        assert_eq!(retrieved_data1.hash, data_record1.hash);
        assert_eq!(retrieved_data1.data, data_record1.data);

        assert_eq!(retrieved_data2.hash, data_record2.hash);
        assert_eq!(retrieved_data2.data, data_record2.data);

        // Clean up MongoDB collections
        let merkle_cname = get_collection_name(MONGODB_MERKLE_NAME_PREFIX.to_string(), test_id);
        let data_cname = get_collection_name(MONGODB_DATA_NAME_PREFIX.to_string(), test_id);

        mongo_db.drop_collection::<MerkleRecord>(MONGODB_DATABASE.to_string(), merkle_cname)?;
        mongo_db.drop_collection::<DataHashRecord>(MONGODB_DATABASE.to_string(), data_cname)?;

        Ok(())
    }
}
