use primitive_types::U256;
use serde::{de::Visitor, Deserialize};

pub fn serialize_u128<S>(num: &u128, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&num.to_string())
}

pub fn deserialize_u128<'de, D>(deserializer: D) -> Result<u128, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let s = <std::string::String as Deserialize>::deserialize(deserializer)?;
    s.parse::<u128>().map_err(serde::de::Error::custom)
}

pub fn serialize_u64<S>(num: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&num.to_string())
}

pub fn deserialize_u64<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let s = <std::string::String as Deserialize>::deserialize(deserializer)?;
    s.parse::<u64>().map_err(serde::de::Error::custom)
}

pub fn serde_serialize_u256<S: serde::Serializer>(u256: &U256, ser: S) -> Result<S::Ok, S::Error> {
    let hex_string = format!("0x{}", hex::encode(u256.to_big_endian()));
    ser.serialize_str(&hex_string)
}

struct U256Visitor;

impl<'de> Visitor<'de> for U256Visitor {
    type Value = U256;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string representing a U256 value")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: ::serde::de::Error,
    {
        let v = v.trim();

        if let Some(hex_val) = v.strip_prefix("0x") {
            let bytes = match hex::decode(hex_val) {
                Ok(b) => b,
                Err(_) => return Err(E::custom("invalid hex string for U256")),
            };

            let mut padded = vec![0; 32];
            let start_idx = padded.len().saturating_sub(bytes.len());
            padded[start_idx..].copy_from_slice(&bytes);

            return Ok(U256::from_big_endian(&padded));
        }

        match v.parse::<U256>() {
            Ok(val) => Ok(val),
            Err(_) => Err(E::custom("failed to parse U256 from string")),
        }
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: ::serde::de::Error,
    {
        self.visit_str(&v)
    }
}

pub fn serde_deserialize_u256<'de, D>(de: D) -> Result<U256, D::Error>
where
    D: serde::Deserializer<'de>,
{
    de.deserialize_str(U256Visitor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitive_types::U256;
    use serde::{Deserialize, Serialize};

    #[test]
    fn test_serialize_deserialize_u128() {
        let value: u128 = 123456789012345678901234567890;
        let json = serde_json::to_string(&value.to_string()).unwrap();

        #[derive(Serialize, Deserialize)]
        struct Wrapper(
            #[serde(
                serialize_with = "serialize_u128",
                deserialize_with = "deserialize_u128"
            )]
            u128,
        );

        let wrapper: Wrapper = serde_json::from_str(&format!("\"{}\"", value)).unwrap();
        assert_eq!(wrapper.0, value);
    }

    #[test]
    fn test_serialize_deserialize_u64() {
        let value: u64 = 9876543210;
        let json = serde_json::to_string(&value.to_string()).unwrap();

        #[derive(Serialize, Deserialize)]
        struct Wrapper(
            #[serde(serialize_with = "serialize_u64", deserialize_with = "deserialize_u64")] u64,
        );

        let wrapper: Wrapper = serde_json::from_str(&format!("\"{}\"", value)).unwrap();
        assert_eq!(wrapper.0, value);
    }

    #[test]
    fn test_serde_serialize_deserialize_u256_decimal() {
        let val = U256::from_dec_str("1234567890123456789012345678901234567890").unwrap();

        #[derive(Serialize, Deserialize)]
        struct Wrapper(
            #[serde(
                serialize_with = "serde_serialize_u256",
                deserialize_with = "serde_deserialize_u256"
            )]
            U256,
        );

        let wrapper = Wrapper(val);
        let json = serde_json::to_string(&wrapper).unwrap();
        let deserialized: Wrapper = serde_json::from_str(&json).unwrap();

        assert_eq!(wrapper.0, deserialized.0);
    }
}
