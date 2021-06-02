use std::fmt;

use lazy_static::lazy_static;

#[derive(PartialEq, Clone, Copy)]
pub enum Function {
    Key,
    KeyOf,
    Search,
    TypeOf,
    Len,
    Hist,
    Str,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Function::Key => write!(f, "key"),
            Function::KeyOf => write!(f, "keyof"),
            Function::Search => write!(f, "search"),
            Function::TypeOf => write!(f, "typeof"),
            Function::Len => write!(f, "len"),
            Function::Hist => write!(f, "hist"),
            Function::Str => write!(f, "str"),
        }
    }
}

lazy_static! {
    pub static ref FUNCTIONS: Vec<Function> = vec![
        Function::Key,
        Function::Search,
        Function::TypeOf,
        Function::KeyOf,
        Function::Len,
        Function::Hist,
        Function::Str,
    ];
}
