use std::str::FromStr;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
pub enum BuiltInType {
    I32,
    I64,
    FP32,
    FP64,
    String,
    Bool,
}

impl FromStr for BuiltInType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "I32" => Ok(BuiltInType::I32),
            "I64" => Ok(BuiltInType::I64),
            "FP32" => Ok(BuiltInType::FP32),
            "FP64" => Ok(BuiltInType::FP64),
            "String" => Ok(BuiltInType::String),
            "Bool" => Ok(BuiltInType::Bool),
            _ => Err(anyhow::anyhow!("unknown type {}", s)),
        }
    }
}

pub fn libc_type_signatures() -> Vec<LibcTypeSignature> {
    let s = include_str!("libc_type_signatures.json");
    serde_json::from_str(s).unwrap()
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LibcTypeSignature {
    pub name: String,
    pub return_type: String,
    pub params: Vec<LibcTypeSignatureParam>,
}

#[derive(Clone, Debug, Deserialize)]
pub struct LibcTypeSignatureParam {
    pub name: String,
    pub r#type: String,
}
