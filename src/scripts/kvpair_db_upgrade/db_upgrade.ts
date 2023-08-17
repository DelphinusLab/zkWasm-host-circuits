import * as mongoDB from "mongodb";

const DB_VERSION = 1;
const DB_CONFIG_COLLECTION_NAME = "DBConfig";
const DB_NAME = "zkwasmkvpair";
const DB_VERSION_NAME = "DBVersion";

/*
 * Current dbversion store in the DBConfig collection: {name: DBVersion, value: 1.0}
 */
async function getDBVersion(db: mongoDB.Db) : Promise<number> {
    let db_config = db.collection(DB_CONFIG_COLLECTION_NAME);
    let query = { "name": DB_VERSION_NAME };
    let verRecord = await db_config.findOne(query);
    if (verRecord) {
        let version = verRecord.value;
        return version;
    }
    else {
        return 0;
    }
}

async function updateDBVersion(db: mongoDB.Db) {
    let db_config = db.collection(DB_CONFIG_COLLECTION_NAME);
    let filter = { "name": DB_VERSION_NAME };
    let replacement = { $set: { "value": DB_VERSION } }
    await db_config.updateOne(filter, replacement, { upsert: true });
}

/*
 * Detail db upgrade script start here.
 */

//Add index hash as a unique index
async function addIndexHashIndex(collection: mongoDB.Collection) {
    const nameRegExp = /^MERKLEDATA_/;
    const INDEX_NAME = "indexHashIndex";
    if (collection.collectionName.match(nameRegExp)) {
        let indexExisted: boolean = await collection.indexExists(INDEX_NAME);
        if(indexExisted) {
            console.log("Delete pre-existing %s for %s", INDEX_NAME, collection.collectionName);
            collection.dropIndex(INDEX_NAME);
        }

        console.log("Begin add %s for %s", INDEX_NAME, collection.collectionName);
        await collection.createIndex(
            {
                "index": 1,
                "hash": -1
            },
            {
                unique: true,
                name: INDEX_NAME
            }
        );
        console.log("Finish add %s for %s", INDEX_NAME, collection.collectionName);
    }
}

(async () => {
    const client: mongoDB.MongoClient = new mongoDB.MongoClient('mongodb://localhost/');
    await client.connect();
    const db: mongoDB.Db = client.db(DB_NAME);
    const dbVersion = await getDBVersion(db);
    let collections: mongoDB.Collection[] = await db.collections();
    for (const collection of collections) {
        if (dbVersion < 1) {
            await addIndexHashIndex(collection);
        }
    }

    //This must be run at the end of upgrade script.
    await updateDBVersion(db);
    console.log("Upgrade finished");
    client.close();
})();