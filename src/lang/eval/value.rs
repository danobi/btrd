use std::convert::TryInto;
use std::fmt;

use anyhow::{anyhow, bail, ensure, Result};

use crate::btrfs::structs::{Field as BtrfsField, Struct as BtrfsStruct, Type as BtrfsType};
use crate::lang::functions::Function;

#[derive(Clone, PartialEq)]
pub enum Value {
    /// All integers are internally represented as 128 bit signed to keep things simple
    ///
    /// Any conversion errors (eg. during demotion, to unsigned) will trigger runtime errors
    Integer(i128),
    String(String),
    Boolean(bool),
    Array(Vec<Value>),
    Function(Function),
    Struct(Struct),
}

impl Value {
    pub fn short_display(&self) -> String {
        match self {
            Value::Array(vec) => format!("[][{}]", vec.len()),
            Value::Struct(s) => format!("struct {}", s.name),
            v => format!("{}", v),
        }
    }

    pub fn as_integer(&self) -> Result<i128> {
        match self {
            Value::Integer(i) => Ok(*i),
            v => bail!("Expected integer, got '{}'", v.short_display()),
        }
    }

    pub fn as_boolean(&self) -> Result<bool> {
        match self {
            Value::Boolean(b) => Ok(*b),
            v => bail!("Expected boolean, got '{}'", v.short_display()),
        }
    }

    pub fn as_string(&self) -> Result<&str> {
        match self {
            Value::String(s) => Ok(s),
            v => bail!("Expected string, got '{}'", v.short_display()),
        }
    }

    pub fn as_vec(&self) -> Result<&[Value]> {
        match self {
            Value::Array(v) => Ok(v),
            v => bail!("Expected array, got '{}'", v.short_display()),
        }
    }

    pub fn as_struct(&self) -> Result<&Struct> {
        match self {
            Value::Struct(s) => Ok(s),
            v => bail!("Expected struct, got '{}'", v.short_display()),
        }
    }

    pub fn as_function(&self) -> Result<&Function> {
        match self {
            Value::Function(func) => Ok(func),
            v => bail!("Expected function, got '{}'", v.short_display()),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Integer(i) => write!(f, "{}", i),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Boolean(b) => {
                write!(f, "{}", if *b { "true" } else { "false" })
            }
            Value::Array(array) => {
                let mut out = String::new();
                out += "[\n";
                for val in array {
                    let val_str = format!("{},", val);
                    for line in val_str.lines() {
                        out += &format!("{}{}\n", indent(1), line);
                    }
                }
                out += "]";

                write!(f, "{}", out)
            }
            Value::Function(func) => write!(f, "{}()", func),
            Value::Struct(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Struct {
    pub name: &'static str,
    /// Disk key for this struct
    ///
    /// `None` for nested structs
    pub key: Option<(i128, i128, i128)>,
    pub fields: Vec<StructField>,
}

impl Struct {
    /// Convert raw bytes into a `Struct`
    ///
    /// The first byte of `bytes` must begin where the struct begins. `bytes` must also contain
    /// _at_least_ `bs.size()` bytes (more is ok).
    pub fn from_bytes(
        bs: &BtrfsStruct,
        key: Option<(i128, i128, i128)>,
        bytes: &[u8],
    ) -> Result<Self> {
        ensure!(
            bs.size() <= bytes.len(),
            "Cannot interpret 'struct {}', not enough bytes provided ({} < {})",
            bs.name,
            bytes.len(),
            bs.size()
        );

        let mut ret = Struct {
            name: bs.name,
            key,
            fields: Vec::with_capacity(bs.fields.len()),
        };

        let mut offset: usize = 0;
        let mut trailing_data: usize = 0;
        for field in &bs.fields {
            if let BtrfsType::TrailingString(n) = &field.ty {
                let mut found = false;

                for processed_field in &ret.fields {
                    if processed_field.name == *n {
                        let string_len = processed_field.value.as_integer()? as usize;
                        let end_of_struct: usize = bs.size() + trailing_data;
                        let end_of_str: usize = string_len + end_of_struct;

                        // So the next trailing string starts at the right offset
                        trailing_data += string_len;

                        ensure!(
                            end_of_str <= bytes.len(),
                            "Cannot interpret 'struct {}', not enough bytes provided for string read ({} < {})",
                            bs.name,
                            bytes.len(),
                            end_of_str
                        );

                        ret.fields.push(StructField {
                            name: field
                                .name
                                .ok_or_else(|| anyhow!("TrailingString can't be anonymous"))?,
                            value: Value::String(
                                String::from_utf8_lossy(&bytes[end_of_struct..end_of_str])
                                    .to_string(),
                            ),
                        });

                        found = true;
                        break;
                    }
                }

                // Should not happen -- there are tests for this
                ensure!(found, "Did not find string len field in struct");
            } else {
                let mut fields = StructField::from_bytes(field, &bytes[offset..])?;
                ret.fields.append(&mut fields);
                offset += field.ty.size();
            }
        }

        Ok(ret)
    }

    pub fn field(&self, name: &str) -> Result<&Value> {
        let name_clone: &str = <&str>::clone(&self.name);

        self.fields
            .iter()
            .find_map(|f| if f.name == name { Some(&f.value) } else { None })
            .ok_or_else(|| anyhow!("Failed to find field '{}' in 'struct {}'", name, name_clone))
    }

    pub fn field_mut(&mut self, name: &str) -> Result<&mut Value> {
        let name_clone: &str = <&str>::clone(&self.name);

        self.fields
            .iter_mut()
            .find_map(|f| {
                if f.name == name {
                    Some(&mut f.value)
                } else {
                    None
                }
            })
            .ok_or_else(|| anyhow!("Failed to find field '{}' in 'struct {}'", name, name_clone))
    }
}

fn indent(level: usize) -> String {
    " ".repeat(level * 4)
}

impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut ret = String::new();

        ret += &format!("struct {} {{\n", self.name);

        for field in &self.fields {
            let val = format!("{},", field.value);
            let mut val_lines = val.lines();

            ret += &format!(
                "{}.{} = {}\n",
                indent(1),
                field.name,
                val_lines.next().expect("Value has no display")
            );

            for line in val_lines {
                ret += &format!("{}{}\n", indent(1), line);
            }
        }

        ret += "}";

        write!(f, "{}", ret)
    }
}

#[derive(Clone, PartialEq)]
pub struct StructField {
    pub name: &'static str,
    pub value: Value,
}

impl StructField {
    /// Convert raw bytes into `StructField`s
    ///
    /// The first byte of `bytes` must begin where the field begins. `bytes` must also contain
    /// _at_least_ `bf.size()` bytes (more is ok).
    ///
    /// Returns a vector b/c anonymous unions / structs are handled as fields of the parent
    /// struct.
    fn from_bytes(bf: &BtrfsField, bytes: &[u8]) -> Result<Vec<Self>> {
        ensure!(
            bf.ty.size() <= bytes.len(),
            "Cannot interpret 'struct {}', not enough bytes provided ({} < {})",
            if let Some(name) = bf.name {
                name
            } else {
                "(anon)"
            },
            bytes.len(),
            bf.ty.size()
        );

        let mut ret = Vec::new();
        let field_val = bf.ty.to_value(bytes)?;

        if let Some(name) = bf.name {
            ret.push(StructField {
                name,
                value: field_val,
            });
        } else {
            match field_val {
                Value::Struct(mut s) => ret.append(&mut s.fields),
                _ => bail!("Only structs can be used as anonymous fields"),
            }
        }

        Ok(ret)
    }
}

impl BtrfsType {
    /// Convert raw bytes into a `Value` based on `self`
    ///
    /// The first byte of `bytes` must begin where the field begins. `bytes` must also contain
    /// _at_least_ `self.size()` bytes (more is ok).
    fn to_value(&self, bytes: &[u8]) -> Result<Value> {
        Ok(match self {
            Self::U8 => Value::Integer(u8::from_le(bytes[0]).into()),
            Self::U16 => Value::Integer(u16::from_le_bytes(bytes[0..2].try_into()?).into()),
            Self::U32 => Value::Integer(u32::from_le_bytes(bytes[0..4].try_into()?).into()),
            Self::U64 => Value::Integer(u64::from_le_bytes(bytes[0..8].try_into()?).into()),
            Self::TrailingString(_) => {
                panic!("Unhandled TrailingString -- should be handled at struct level")
            }
            Self::Array(t, n) => {
                let tsize = t.size();
                let mut ret = Vec::with_capacity(*n);
                for i in 0..*n {
                    ret.push(t.to_value(&bytes[i * tsize..])?);
                }

                Value::Array(ret)
            }
            Self::Struct(s) => Value::Struct(Struct::from_bytes(s, None, bytes)?),
            // We do not support named unions, so translate a union type as a struct with fields
            // all constructed from the same offset
            Self::Union(u) => {
                let mut ret = Struct {
                    name: u.name,
                    key: None,
                    fields: Vec::with_capacity(u.fields.len()),
                };

                for field in &u.fields {
                    ret.fields
                        .append(&mut StructField::from_bytes(field, bytes)?);
                }

                Value::Struct(ret)
            }
        })
    }
}
