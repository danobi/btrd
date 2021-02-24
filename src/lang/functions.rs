use std::fmt;

use lazy_static::lazy_static;

#[derive(PartialEq, Clone, Copy)]
pub enum Function {
    Key,
    Search,
    Type,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Function::Key => write!(f, "key"),
            Function::Search => write!(f, "search"),
            Function::Type => write!(f, "type"),
        }
    }
}

lazy_static! {
    pub static ref FUNCTIONS: Vec<Function> = vec![Function::Key, Function::Search, Function::Type];
}
