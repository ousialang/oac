use std::str::FromStr;

use serde::Serialize;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub enum BuiltInType {
    Int,
    String,
}

impl FromStr for BuiltInType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "I32" => Ok(BuiltInType::Int),
            "String" => Ok(BuiltInType::String),
            _ => Err(anyhow::anyhow!("unknown type {}", s)),
        }
    }
}
