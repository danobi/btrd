use std::convert::TryFrom;
use std::fmt;

use anyhow::{bail, Error, Result};
use lazy_static::lazy_static;

#[derive(PartialEq, Clone, Copy)]
pub enum Function {
    Key,
    Search,
}

impl TryFrom<&str> for Function {
    type Error = Error;

    fn try_from(f: &str) -> Result<Self> {
        Ok(match f {
            "key" => Self::Key,
            "search" => Self::Search,
            _ => bail!("Unknown function: {}", f),
        })
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Function::Key => write!(f, "key"),
            Function::Search => write!(f, "search"),
        }
    }
}

lazy_static! {
    pub static ref FUNCTIONS: Vec<Function> = vec![Function::Key, Function::Search,];
}
