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
    Void,
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
            "Void" => Ok(BuiltInType::Void),
            _ => Err(anyhow::anyhow!("unknown type {}", s)),
        }
    }
}
