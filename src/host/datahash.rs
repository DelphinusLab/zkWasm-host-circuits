use std::cell::RefCell;
use std::rc::Rc;

use ff::PrimeField;
use halo2_proofs::pairing::bn256::Fr;
use mongodb::bson::doc;
use mongodb::bson::{spec::BinarySubtype, Bson};
use serde::{
    de::{Error, Unexpected},
    Deserialize, Deserializer, Serialize, Serializer,
};

//use lazy_static;
use crate::host::db::{MongoDB, TreeDB};
use crate::host::poseidon::POSEIDON_HASHER;

fn deserialize_u256_from_binary<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok(bytes.bytes.try_into().unwrap()),
        Ok(..) => Err(Error::invalid_value(Unexpected::Enum, &"Bson::Binary")),
        Err(e) => Err(e),
    }
}

fn deserialize_bytes_from_binary<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    match Bson::deserialize(deserializer) {
        Ok(Bson::Binary(bytes)) => Ok(bytes.bytes.to_vec()),
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

/*
fn hash_to_bson(x: &[u8; 32]) -> Bson {
    Bson::Binary(mongodb::bson::Binary {
        subtype: BinarySubtype::Generic,
        bytes: (*x).into(),
    })
}
*/

#[derive(Clone)]
pub struct MongoDataHash {
    db: Rc<RefCell<dyn TreeDB>>,
}

impl PartialEq for DataHashRecord {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl MongoDataHash {
    pub fn construct(addr: [u8; 32], db: Option<Rc<RefCell<dyn TreeDB>>>) -> Self {
        MongoDataHash {
            db: db.unwrap_or_else(|| Rc::new(RefCell::new(MongoDB::new(addr, None)))),
        }
    }

    pub fn get_record(&self, hash: &[u8; 32]) -> Result<Option<DataHashRecord>, anyhow::Error> {
        let record = self.db.borrow().get_data_record(hash);
        record
    }

    /* We always insert new record as there might be uncommitted update to the merkle tree */
    pub fn update_record(&mut self, record: DataHashRecord) -> Result<(), anyhow::Error> {
        self.db.borrow_mut().set_data_record(record.clone())?;
        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DataHashRecord {
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_u256_from_binary")]
    #[serde(rename = "_id")]
    pub hash: [u8; 32],
    #[serde(serialize_with = "self::serialize_bytes_as_binary")]
    #[serde(deserialize_with = "self::deserialize_bytes_from_binary")]
    pub data: Vec<u8>,
}

impl DataHashRecord {
    /// 将DataHashRecord转换为Vec<u8>
    pub fn to_slice(&self) -> Vec<u8> {
        let mut result = Vec::new();

        // 序列化hash ([u8; 32])
        result.extend_from_slice(&self.hash);

        // 序列化data (Vec<u8>)
        // 首先序列化长度，使用u32表示（4字节）
        let data_len = self.data.len() as u32;
        result.extend_from_slice(&data_len.to_le_bytes());

        // 然后序列化数据内容
        result.extend_from_slice(&self.data);

        result
    }

    /// 从Vec<u8>转换回DataHashRecord
    pub fn from_slice(slice: &[u8]) -> Result<Self, anyhow::Error> {
        if slice.len() < 32 {
            return Err(anyhow::anyhow!("Slice too short for hash"));
        }

        let mut pos = 0;

        // 反序列化hash
        let mut hash = [0u8; 32];
        hash.copy_from_slice(&slice[pos..pos+32]);
        pos += 32;

        // 反序列化data
        // 首先读取长度
        if slice.len() < pos + 4 {
            return Err(anyhow::anyhow!("Slice too short for data length"));
        }
        let mut len_bytes = [0u8; 4];
        len_bytes.copy_from_slice(&slice[pos..pos+4]);
        let data_len = u32::from_le_bytes(len_bytes) as usize;
        pos += 4;

        // 然后读取数据内容
        if slice.len() < pos + data_len {
            return Err(anyhow::anyhow!("Slice too short for data content"));
        }
        let data = slice[pos..pos+data_len].to_vec();

        Ok(DataHashRecord {
            hash,
            data,
        })
    }
}

impl DataHashRecord {
    pub fn new(&mut self, data: &Vec<u8>) -> Self {
        let mut hasher = POSEIDON_HASHER.clone();
        let batchdata = data
            .chunks(16)
            .into_iter()
            .map(|x| {
                let mut v = x.to_vec();
                v.extend_from_slice(&[0u8; 16]);
                let f = v.try_into().unwrap();
                Fr::from_repr(f).unwrap()
            })
            .collect::<Vec<Fr>>();
        hasher.update(&batchdata.as_slice());
        DataHashRecord {
            data: data.clone().try_into().unwrap(),
            hash: hasher.squeeze().to_repr(),
        }
    }
    pub fn data_as_u64(&self) -> [u64; 4] {
        [
            u64::from_le_bytes(self.data[0..8].try_into().unwrap()),
            u64::from_le_bytes(self.data[8..16].try_into().unwrap()),
            u64::from_le_bytes(self.data[16..24].try_into().unwrap()),
            u64::from_le_bytes(self.data[24..32].try_into().unwrap()),
        ]
    }
}

#[cfg(test)]
mod tests {}
