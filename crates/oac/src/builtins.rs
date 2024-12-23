use std::str::FromStr;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
pub enum BuiltInType {
    Int,
    I64,
    String,
}

impl FromStr for BuiltInType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "I32" => Ok(BuiltInType::Int),
            "I64" => Ok(BuiltInType::I64),
            "String" => Ok(BuiltInType::String),
            _ => Err(anyhow::anyhow!("unknown type {}", s)),
        }
    }
}

pub fn libc_type_signatures() -> Vec<LibcTypeSignature> {
    let file = std::fs::read_to_string("src/libc_type_signatures.json").unwrap();
    serde_json::from_str(&file).unwrap()
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LibcTypeSignature {
    pub name: String,
    pub return_type: BuiltInType,
    pub params: Vec<LibcTypeSignatureParam>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct LibcTypeSignatureParam {
    pub name: String,
    pub r#type: BuiltInType,
}
