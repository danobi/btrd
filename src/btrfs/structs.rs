use anyhow::Result;

/// Represents a btrfs constant (usually defined as a macro in btrfs_tree.h)
pub struct Constant {
    pub name: &'static str,
    /// btrd internally represents all integers as signed 128 bit. This should be enough to hold
    /// all btrfs on disk integer types -- I haven't seen any go above 64 bit unsigned.
    pub value: i128,
}

/// Represents an on-disk btrfs type
#[derive(Clone)]
pub enum Type {
    /// NB: little endian
    U8,
    /// NB: little endian
    U16,
    /// NB: little endian
    U32,
    /// NB: little endian
    U64,
    /// (type of elem, number of elems)
    Array(Box<Type>, usize),
    Struct(Struct),
    Union(Union),
    /// A non-nul terminated string at the end of the struct, param is the name of the field in the
    /// struct that contains the length
    TrailingString(&'static str),
    /// Array of trailing types, second param is the name of the field that contains the count
    TrailingTypes(Box<Type>, &'static str),
    /// Dynamically determine fields of a struct
    ///
    /// Used for structs whose layout can only be known after seeing the bytes.
    ///
    /// NB: the returned fields must be statically sized.
    DynamicStruct(fn(&[u8]) -> Result<Vec<Field>>),
}

impl Type {
    /// Returns size of the type in bytes
    pub fn size(&self) -> usize {
        match self {
            Type::U8 => 1,
            Type::U16 => 2,
            Type::U32 => 4,
            Type::U64 => 8,
            // A trailing string is always at the end of the struct -- it's not technically a
            // part of the struct itself so the size is 0
            Type::TrailingString(_) => 0,
            Type::Array(t, n) => t.size() * n,
            Type::Struct(s) => s.size(),
            Type::Union(u) => u.size(),
            // Trailing types are not part of the struct
            Type::TrailingTypes(_, _) => 0,
            // No way we can know the size before runtime
            Type::DynamicStruct(_) => 0,
        }
    }

    /// Whether or not this type's size is statically known
    pub fn is_static_sized(&self) -> bool {
        match self {
            Type::U8 | Type::U16 | Type::U32 | Type::U64 => true,
            Type::Array(t, _) => t.is_static_sized(),
            Type::Struct(s) => s.is_static_sized(),
            Type::Union(u) => u.is_static_sized(),
            Type::TrailingString(_) | Type::TrailingTypes(_, _) | Type::DynamicStruct(_) => false,
        }
    }
}

/// Represents a field in a on-disk btrfs struct
#[derive(Clone)]
pub struct Field {
    /// `None` here implies anonymous struct/union -- a field access on a struct should look
    /// directly at the anonymous struct/union 's fields
    pub name: Option<&'static str>,
    pub ty: Type,
}

/// Represents an on-disk btrfs union
///
/// Note that all on-disk unions are packed (no padding or alignment)
///
/// Also note that btrfs doesn't really have "bare" unions -- unions are typically used inside a
/// struct
#[derive(Clone)]
pub struct Union {
    pub name: &'static str,
    /// Fields in this union
    pub fields: Vec<Field>,
}

impl Union {
    // Returns size of struct in bytes
    //
    // NB: This assumes that all unions are packed (which they are for btrfs)
    pub fn size(&self) -> usize {
        self.fields
            .iter()
            .max_by_key(|f| f.ty.size())
            .map_or(0, |f| f.ty.size())
    }

    /// Whether or not this union's size is statically known
    pub fn is_static_sized(&self) -> bool {
        self.fields.iter().all(|f| f.ty.is_static_sized())
    }
}

/// Represents an on-disk btrfs struct
///
/// Note that all on-disk structs are packed (no padding between fields)
#[derive(Clone)]
pub struct Struct {
    pub name: &'static str,
    /// Given a key (objectid, type, offset), return whether or not this struct belongs to the key
    pub key_match: fn(i128, i128, i128) -> bool,
    /// Fields in this struct
    pub fields: Vec<Field>,
}

impl Struct {
    // Returns size of struct in bytes
    //
    // NB: This assumes that all structs are packed (which they are for btrfs)
    pub fn size(&self) -> usize {
        self.fields.iter().fold(0, |acc, f| acc + f.ty.size())
    }

    /// Whether or not this struct's size is statically known
    pub fn is_static_sized(&self) -> bool {
        self.fields.iter().all(|f| f.ty.is_static_sized())
    }
}

#[test]
fn test_type_size() {
    {
        let t = Type::U8;
        assert_eq!(t.size(), 1);
    }
    {
        let t = Type::U32;
        assert_eq!(t.size(), 4);
    }
    {
        let t = Type::U64;
        assert_eq!(t.size(), 8);
    }
    {
        let t = Type::Array(Box::new(Type::U8), 5);
        assert_eq!(t.size(), 5);
    }
    {
        let t = Type::Array(Box::new(Type::U32), 5);
        assert_eq!(t.size(), 20);
    }
    {
        let s = Struct {
            name: "foo",
            key_match: |_, _, _| false,
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f2"),
                    ty: Type::U8,
                },
            ],
        };
        let t = Type::Struct(s);
        assert_eq!(t.size(), 5);
    }
    {
        let s = Struct {
            name: "foo",
            key_match: |_, _, _| false,
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f2"),
                    ty: Type::U8,
                },
            ],
        };
        let t = Type::Array(Box::new(Type::Struct(s)), 4);
        assert_eq!(t.size(), 20);
    }
    {
        let u = Union {
            name: "foo",
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f2"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("f3"),
                    ty: Type::U64,
                },
            ],
        };
        let t = Type::Union(u);
        assert_eq!(t.size(), 8);
    }
    {
        let u = Union {
            name: "union_one",
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f1"),
                    ty: Type::U8,
                },
            ],
        };
        let uu = Union {
            name: "union_two",
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("f1"),
                    ty: Type::U16,
                },
            ],
        };
        let s = Struct {
            name: "foo",
            key_match: |_, _, _| false,
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::Union(u),
                },
                Field {
                    name: Some("f2"),
                    ty: Type::Union(uu),
                },
            ],
        };
        let t = Type::Struct(s);
        assert_eq!(t.size(), 6);
    }
    {
        let s = Struct {
            name: "foo",
            key_match: |_, _, _| false,
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f2"),
                    ty: Type::U8,
                },
            ],
        };
        let ss = Struct {
            name: "bar",
            key_match: |_, _, _| false,
            fields: vec![
                Field {
                    name: Some("f1"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("f2"),
                    ty: Type::Struct(s),
                },
            ],
        };
        let t = Type::Struct(ss);
        assert_eq!(t.size(), 9);
    }
}
