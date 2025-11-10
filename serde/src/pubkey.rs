use arch_program::pubkey::Pubkey;
use serde::Deserialize;

pub fn serialize_pubkey_hex<S>(pubkey: &Pubkey, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&hex::encode(pubkey.0))
}

pub fn deserialize_pubkey_hex<'de, D>(deserializer: D) -> Result<Pubkey, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let hex_str = <std::string::String as Deserialize>::deserialize(deserializer)?;
    let bytes = hex::decode(&hex_str).map_err(serde::de::Error::custom)?;
    if bytes.len() != 32 {
        return Err(serde::de::Error::custom(format!(
            "Invalid pubkey length: expected 32 bytes, got {}",
            bytes.len()
        )));
    }
    let mut array = [0u8; 32];
    array.copy_from_slice(&bytes);
    Ok(Pubkey::from(array))
}

#[cfg(test)]
mod tests {
    use super::*;
    use arch_program::pubkey::Pubkey;
    use serde::{Deserialize, Serialize};

    #[test]
    fn test_serialize_deserialize_pubkey_hex() {
        let key_bytes = [0xABu8; 32];
        let pubkey = Pubkey::from(key_bytes);

        #[derive(Serialize, Deserialize)]
        struct Wrapper(
            #[serde(
                serialize_with = "serialize_pubkey_hex",
                deserialize_with = "deserialize_pubkey_hex"
            )]
            Pubkey,
        );

        let wrapper = Wrapper(pubkey);
        let json = serde_json::to_string(&wrapper).unwrap();
        let expected_hex = hex::encode(key_bytes);
        assert!(json.contains(&expected_hex));

        let deserialized: Wrapper = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.0, pubkey);
    }

    #[test]
    fn test_deserialize_pubkey_hex_invalid_length() {
        let json = r#""deadbeef""#; // Too short
        let result: Result<Pubkey, _> = serde_json::from_str(json);
        assert!(result.is_err());
    }
}
