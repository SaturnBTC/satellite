use arch_program::utxo::UtxoMeta;
use bitcoin::Txid;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use std::str::FromStr;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UtxoMetaJson {
    pub txid: Txid,
    pub vout: u32,
}

pub fn serialize_utxo_meta<S>(utxo: &UtxoMeta, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let utxo_info_json = UtxoMetaJson {
        txid: Txid::from_str(&hex::encode(&utxo.txid())).unwrap(),
        vout: utxo.vout(),
    };

    utxo_info_json.serialize(serializer)
}

pub fn deserialize_utxo_meta<'de, D>(deserializer: D) -> Result<UtxoMeta, D::Error>
where
    D: Deserializer<'de>,
{
    let utxo_info_json = UtxoMetaJson::deserialize(deserializer)?;

    let utxo = UtxoMeta::from_outpoint(utxo_info_json.txid, utxo_info_json.vout);

    Ok(utxo)
}

pub fn serialize_utxo_meta_vec<S>(utxos: &Vec<UtxoMeta>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let utxo_info_jsons: Vec<UtxoMetaJson> = utxos
        .iter()
        .map(|utxo| UtxoMetaJson {
            txid: Txid::from_str(&hex::encode(&utxo.txid())).unwrap(),
            vout: utxo.vout(),
        })
        .collect();

    utxo_info_jsons.serialize(serializer)
}

pub fn deserialize_utxo_meta_vec<'de, D>(deserializer: D) -> Result<Vec<UtxoMeta>, D::Error>
where
    D: Deserializer<'de>,
{
    let utxo_info_jsons = Vec::<UtxoMetaJson>::deserialize(deserializer)?;

    let utxos = utxo_info_jsons
        .into_iter()
        .map(|json| UtxoMeta::from_outpoint(json.txid, json.vout))
        .collect();

    Ok(utxos)
}

pub fn serialize_utxo_meta_array<S>(utxos: &[UtxoMeta], serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let utxo_info_jsons: Vec<UtxoMetaJson> = utxos
        .iter()
        .map(|utxo| UtxoMetaJson {
            txid: Txid::from_str(&hex::encode(&utxo.txid())).unwrap(),
            vout: utxo.vout(),
        })
        .collect();

    utxo_info_jsons.serialize(serializer)
}

pub fn deserialize_utxo_meta_array<'de, D, const N: usize>(
    deserializer: D,
) -> Result<[UtxoMeta; N], D::Error>
where
    D: Deserializer<'de>,
{
    let utxo_info_jsons = Vec::<UtxoMetaJson>::deserialize(deserializer)?;
    let utxos = std::array::from_fn(|i| {
        let json = utxo_info_jsons.get(i).unwrap();

        UtxoMeta::from_outpoint(json.txid, json.vout)
    });

    Ok(utxos)
}

pub fn serialize_optional_utxo_meta<S>(
    utxo_meta_option: &Option<UtxoMeta>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match utxo_meta_option {
        Some(utxo_meta) => {
            use serde::Serialize;

            let utxo_json = UtxoMetaJson {
                txid: Txid::from_str(&hex::encode(&utxo_meta.txid())).unwrap(),
                vout: utxo_meta.vout(),
            };
            #[derive(Serialize)]
            struct Wrapper<'a>(&'a UtxoMetaJson);
            Wrapper(&utxo_json).serialize(serializer)
        }
        None => serializer.serialize_none(),
    }
}

pub fn deserialize_optional_utxo_meta<'de, D>(deserializer: D) -> Result<Option<UtxoMeta>, D::Error>
where
    D: Deserializer<'de>,
{
    let utxo_json_option = Option::<UtxoMetaJson>::deserialize(deserializer)?;

    match utxo_json_option {
        Some(json) => Ok(Some(UtxoMeta::from_outpoint(json.txid, json.vout))),
        None => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};
    use serde_json::{from_str, to_string};
    use std::str::FromStr;

    #[derive(Serialize, Deserialize, Debug, PartialEq)]
    struct SingleUtxoWrapper {
        #[serde(
            serialize_with = "serialize_utxo_meta",
            deserialize_with = "deserialize_utxo_meta"
        )]
        utxo: UtxoMeta,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq)]
    struct VecUtxoWrapper {
        #[serde(
            serialize_with = "serialize_utxo_meta_vec",
            deserialize_with = "deserialize_utxo_meta_vec"
        )]
        utxos: Vec<UtxoMeta>,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq)]
    struct ArrayUtxoWrapper<const N: usize> {
        #[serde(
            serialize_with = "serialize_utxo_meta_array",
            deserialize_with = "deserialize_utxo_meta_array"
        )]
        utxos: [UtxoMeta; N],
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq)]
    struct OptionalUtxoWrapper {
        #[serde(
            serialize_with = "serialize_optional_utxo_meta",
            deserialize_with = "deserialize_optional_utxo_meta"
        )]
        utxo: Option<UtxoMeta>,
    }

    fn mk_utxo(txid_hex: &str, vout: u32) -> UtxoMeta {
        let txid = Txid::from_str(txid_hex).unwrap();
        UtxoMeta::from_outpoint(txid, vout)
    }

    #[test]
    fn test_serialize_deserialize_single_utxo() {
        let utxo = mk_utxo(
            "c5cc9251192330191366016c8dab0f67dc345bd024a206c313dbf26db0a66bb1",
            0,
        );
        let wrapper = SingleUtxoWrapper { utxo };

        let json = to_string(&wrapper).unwrap();
        assert_eq!(
            json,
            "{\"utxo\":{\"txid\":\"c5cc9251192330191366016c8dab0f67dc345bd024a206c313dbf26db0a66bb1\",\"vout\":0}}"
        );

        let decoded: SingleUtxoWrapper = from_str(&json).unwrap();
        assert_eq!(decoded, wrapper);
    }

    #[test]
    fn test_serialize_deserialize_vec_utxo() {
        let u1 = mk_utxo(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            1,
        );
        let u2 = mk_utxo(
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            2,
        );

        let wrapper = VecUtxoWrapper {
            utxos: vec![u1, u2],
        };
        let json = to_string(&wrapper).unwrap();
        assert_eq!(
            json,
            "{\"utxos\":[{\"txid\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",\"vout\":1},{\"txid\":\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\",\"vout\":2}]}"
        );

        let decoded: VecUtxoWrapper = from_str(&json).unwrap();
        assert_eq!(decoded, wrapper);

        // also check empty vec
        let empty = VecUtxoWrapper { utxos: vec![] };
        let json_empty = to_string(&empty).unwrap();
        assert_eq!(json_empty, "{\"utxos\":[]}");
        let decoded_empty: VecUtxoWrapper = from_str(&json_empty).unwrap();
        assert_eq!(decoded_empty, empty);
    }

    #[test]
    fn test_serialize_deserialize_array_utxo() {
        let u1 = mk_utxo(
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            3,
        );
        let u2 = mk_utxo(
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
            4,
        );

        let wrapper = ArrayUtxoWrapper { utxos: [u1, u2] };
        let json = to_string(&wrapper).unwrap();
        assert_eq!(
            json,
            "{\"utxos\":[{\"txid\":\"cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\",\"vout\":3},{\"txid\":\"dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\",\"vout\":4}]}"
        );

        let decoded: ArrayUtxoWrapper<2> = from_str(&json).unwrap();
        assert_eq!(decoded, wrapper);
    }

    #[test]
    fn test_serialize_deserialize_optional_utxo() {
        // Some
        let some_wrapper = OptionalUtxoWrapper {
            utxo: Some(mk_utxo(
                "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
                5,
            )),
        };
        let json_some = to_string(&some_wrapper).unwrap();
        assert_eq!(
            json_some,
            "{\"utxo\":{\"txid\":\"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee\",\"vout\":5}}"
        );
        let decoded_some: OptionalUtxoWrapper = from_str(&json_some).unwrap();
        assert_eq!(decoded_some, some_wrapper);

        // None
        let none_wrapper = OptionalUtxoWrapper { utxo: None };
        let json_none = to_string(&none_wrapper).unwrap();
        assert_eq!(json_none, "{\"utxo\":null}");
        let decoded_none: OptionalUtxoWrapper = from_str(&json_none).unwrap();
        assert_eq!(decoded_none, none_wrapper);
    }
}
