use mongodb::{
    bson::doc,
    sync::{Client, Collection},
};

const MONGODB_URI: &str = "mongodb://localhost:27017";

lazy_static::lazy_static! {
    pub static ref CLIENT: Client= Client::with_uri_str(MONGODB_URI).expect("Unexpected DB Error");
}

pub fn get_collection<T>(
    database: String,
    name: String,
) -> Result<Collection<T>, mongodb::error::Error> {
    let database = CLIENT.database(database.as_str());
    let collection = database.collection::<T>(name.as_str());
    Ok(collection)
}
