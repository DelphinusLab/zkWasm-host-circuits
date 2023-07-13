/*
  **********Upgrade functions**********
*/
function addIndexHashIndex(collectionName) {
    const nameRegExp = /^MERKLEDATA_/;
    if (collectionName.match(nameRegExp)) {
        console.log("Begin addIndexHashIndex for", collectionName);
        db[collectionName].createIndex(
            {
                "index": 1,
                "hash": -1
            },
            {
                name: "indexHashIndex"
            }
        );
    }
}

/*
  **********Run on all collections**********
*/
db = connect('mongodb://localhost/zkwasmkvpair');
let collections = db.getCollectionNames();

collections.forEach(addIndexHashIndex);
console.log("addIndexHashIndex finished.");