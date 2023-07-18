import * as mongoDB from "mongodb";

async function addIndexHashIndex(collection: mongoDB.Collection) {
    const nameRegExp = /^MERKLEDATA_/;
    if (collection.collectionName.match(nameRegExp)) {
        console.log("Begin addIndexHashIndex for", collection.collectionName);
        await collection.createIndex(
            {
                "index": 1,
                "hash": -1
            },
            {
                unique: false,
                name: "indexHashIndex"
            }
        );
        console.log("Finish addIndexHashIndex for", collection.collectionName);
    }
}

(async () => {
    const client: mongoDB.MongoClient = new mongoDB.MongoClient('mongodb://localhost/');
    await client.connect();
    const db: mongoDB.Db = client.db("zkwasmkvpair");
    let collections: mongoDB.Collection[] = await db.collections();
    for (const collection of collections) {
        await addIndexHashIndex(collection);
    }
    console.log("Upgrade finished");
    client.close();
})();