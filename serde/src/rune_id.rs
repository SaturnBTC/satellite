use arch_program::rune::RuneId;
use serde::Deserialize;

use std::str::FromStr;

pub fn serialize_rune_id<S>(rune_id: &RuneId, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&rune_id.to_string())
}

pub fn deserialize_rune_id<'de, D>(deserializer: D) -> Result<RuneId, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let s = <std::string::String as Deserialize>::deserialize(deserializer)?;
    RuneId::from_str(&s).map_err(serde::de::Error::custom)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[test]
    fn test_serialize_deserialize_rune_id() {
        let rune = RuneId::new(840_000u64, 12u32);

        #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
        struct Wrapper(
            #[serde(
                serialize_with = "serialize_rune_id",
                deserialize_with = "deserialize_rune_id"
            )]
            RuneId,
        );

        let wrapper = Wrapper(rune);
        let json = serde_json::to_string(&wrapper).unwrap();
        assert!(json.contains("840000:12"));

        let decoded: Wrapper = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded, wrapper);
    }
}

