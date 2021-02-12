use std::fmt;

#[derive(PartialEq, Clone)]
pub struct IntegerType {}

impl fmt::Display for IntegerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "integer")
    }
}

#[derive(PartialEq, Clone)]
pub struct StringType {}

impl fmt::Display for StringType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "string")
    }
}

#[derive(PartialEq, Clone)]
pub struct BooleanType {}

impl fmt::Display for BooleanType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "boolean")
    }
}

#[derive(PartialEq, Clone)]
pub enum Type {
    Integer(IntegerType),
    String(StringType),
    Boolean(BooleanType),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Integer(t) => write!(f, "{}", t),
            Type::String(t) => write!(f, "{}", t),
            Type::Boolean(t) => write!(f, "{}", t),
        }
    }
}
