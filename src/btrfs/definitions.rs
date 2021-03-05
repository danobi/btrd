//! This module defines all the on-disk btrfs structures
//!
//! Useful references are /usr/include/linux/btrfs_tree.h and
//! https://github.com/btrfs/btrfs-dev-docs/blob/master/tree-items.txt .
//!
//! NB: Nested structs must also be included as a top level struct. Otherwise, chained field
//! accesses may not work (ie for `struct_foo.nested.field`, `struct_foo.nested` may not be
//! resolved as a valid struct if the type of `struct_foo.nested` is not found in `STRUCTS`).
//!
//! Note that we do not handle trailing structures yet. IOW, if a structure has trailing elements
//! (the type of which depend on the primary structure), it's not handled yet. There are plans to
//! do so.

use super::structs::{Constant, Field, Struct, Type, Union};

use anyhow::Result;
use lazy_static::lazy_static;

const BTRFS_DEV_STAT_WRITE_ERRS: u8 = 0;
const BTRFS_DEV_STAT_READ_ERRS: u8 = 1;
const BTRFS_DEV_STAT_FLUSH_ERRS: u8 = 2;
const BTRFS_DEV_STAT_CORRUPTION_ERRS: u8 = 3;
const BTRFS_DEV_STAT_GENERATION_ERRS: u8 = 4;
const BTRFS_DEV_STAT_VALUES_MAX: u8 = 5;
const BTRFS_CSUM_TYPE_CRC32: i128 = 0;
const BTRFS_CSUM_TYPE_XXHASH: i128 = 1;
const BTRFS_CSUM_TYPE_SHA256: i128 = 2;
const BTRFS_CSUM_TYPE_BLAKE2: i128 = 3;
const BTRFS_FILE_EXTENT_INLINE: i128 = 0;
const BTRFS_FILE_EXTENT_REG: i128 = 1;
const BTRFS_FILE_EXTENT_PREALLOC: i128 = 2;
const BTRFS_NR_FILE_EXTENT_TYPES: i128 = 3;
const BTRFS_RAID_RAID10: i128 = 0;
const BTRFS_RAID_RAID1: i128 = 1;
const BTRFS_RAID_DUP: i128 = 2;
const BTRFS_RAID_RAID0: i128 = 3;
const BTRFS_RAID_SINGLE: i128 = 4;
const BTRFS_RAID_RAID5: i128 = 5;
const BTRFS_RAID_RAID6: i128 = 6;
const BTRFS_RAID_RAID1C3: i128 = 7;
const BTRFS_RAID_RAID1C4: i128 = 8;
const BTRFS_NR_RAID_TYPES: i128 = 9;
const BTRFS_UUID_SIZE: u8 = 16;
const BTRFS_ROOT_TREE_OBJECTID: i128 = 1;
const BTRFS_EXTENT_TREE_OBJECTID: i128 = 2;
const BTRFS_CHUNK_TREE_OBJECTID: i128 = 3;
const BTRFS_DEV_TREE_OBJECTID: i128 = 4;
const BTRFS_FS_TREE_OBJECTID: i128 = 5;
const BTRFS_ROOT_TREE_DIR_OBJECTID: i128 = 6;
const BTRFS_CSUM_TREE_OBJECTID: i128 = 7;
const BTRFS_QUOTA_TREE_OBJECTID: i128 = 8;
const BTRFS_UUID_TREE_OBJECTID: i128 = 9;
const BTRFS_FREE_SPACE_TREE_OBJECTID: i128 = 10;
const BTRFS_DEV_STATS_OBJECTID: i128 = 0;
const BTRFS_BALANCE_OBJECTID: i128 = 4;
const BTRFS_ORPHAN_OBJECTID: i128 = 5;
const BTRFS_TREE_LOG_OBJECTID: i128 = 6;
const BTRFS_TREE_LOG_FIXUP_OBJECTID: i128 = 7;
const BTRFS_TREE_RELOC_OBJECTID: i128 = 8;
const BTRFS_DATA_RELOC_TREE_OBJECTID: i128 = 9;
const BTRFS_EXTENT_CSUM_OBJECTID: u64 = 0u64.overflowing_sub(10).0;
const BTRFS_FREE_SPACE_OBJECTID: u64 = 0u64.overflowing_sub(11).0;
const BTRFS_FREE_INO_OBJECTID: u64 = 0u64.overflowing_sub(12).0;
const BTRFS_MULTIPLE_OBJECTIDS: u64 = 0u64.overflowing_sub(255).0;
const BTRFS_FIRST_FREE_OBJECTID: i128 = 256;
const BTRFS_LAST_FREE_OBJECTID: u64 = 0u64.overflowing_sub(256).0;
const BTRFS_FIRST_CHUNK_TREE_OBJECTID: i128 = 256;
const BTRFS_DEV_ITEMS_OBJECTID: i128 = 1;
const BTRFS_BTREE_INODE_OBJECTID: i128 = 1;
const BTRFS_EMPTY_SUBVOL_DIR_OBJECTID: i128 = 2;
const BTRFS_DEV_REPLACE_DEVID: i128 = 0;
const BTRFS_INODE_ITEM_KEY: i128 = 1;
const BTRFS_INODE_REF_KEY: i128 = 12;
const BTRFS_INODE_EXTREF_KEY: i128 = 13;
const BTRFS_XATTR_ITEM_KEY: i128 = 24;
const BTRFS_ORPHAN_ITEM_KEY: i128 = 48;
const BTRFS_DIR_LOG_ITEM_KEY: i128 = 60;
const BTRFS_DIR_LOG_INDEX_KEY: i128 = 72;
const BTRFS_DIR_ITEM_KEY: i128 = 84;
const BTRFS_DIR_INDEX_KEY: i128 = 96;
const BTRFS_EXTENT_DATA_KEY: i128 = 108;
const BTRFS_EXTENT_CSUM_KEY: i128 = 128;
const BTRFS_ROOT_ITEM_KEY: i128 = 132;
const BTRFS_ROOT_BACKREF_KEY: i128 = 144;
const BTRFS_ROOT_REF_KEY: i128 = 156;
const BTRFS_EXTENT_ITEM_KEY: i128 = 168;
const BTRFS_METADATA_ITEM_KEY: i128 = 169;
const BTRFS_TREE_BLOCK_REF_KEY: i128 = 176;
const BTRFS_EXTENT_DATA_REF_KEY: i128 = 178;
const BTRFS_EXTENT_REF_V0_KEY: i128 = 180;
const BTRFS_SHARED_BLOCK_REF_KEY: i128 = 182;
const BTRFS_SHARED_DATA_REF_KEY: i128 = 184;
const BTRFS_BLOCK_GROUP_ITEM_KEY: i128 = 192;
const BTRFS_FREE_SPACE_INFO_KEY: i128 = 198;
const BTRFS_FREE_SPACE_EXTENT_KEY: i128 = 199;
const BTRFS_FREE_SPACE_BITMAP_KEY: i128 = 200;
const BTRFS_DEV_EXTENT_KEY: i128 = 204;
const BTRFS_DEV_ITEM_KEY: i128 = 216;
const BTRFS_CHUNK_ITEM_KEY: i128 = 228;
const BTRFS_QGROUP_STATUS_KEY: i128 = 240;
const BTRFS_QGROUP_INFO_KEY: i128 = 242;
const BTRFS_QGROUP_LIMIT_KEY: i128 = 244;
const BTRFS_QGROUP_RELATION_KEY: i128 = 246;
const BTRFS_BALANCE_ITEM_KEY: i128 = 248;
const BTRFS_TEMPORARY_ITEM_KEY: i128 = 248;
const BTRFS_DEV_STATS_KEY: i128 = 249;
const BTRFS_PERSISTENT_ITEM_KEY: i128 = 249;
const BTRFS_DEV_REPLACE_KEY: i128 = 250;
const BTRFS_UUID_KEY_SUBVOL: i128 = 251;
const BTRFS_UUID_KEY_RECEIVED_SUBVOL: i128 = 252;
const BTRFS_STRING_ITEM_KEY: i128 = 253;
const BTRFS_CSUM_SIZE: i128 = 32;
const BTRFS_FT_UNKNOWN: i128 = 0;
const BTRFS_FT_REG_FILE: i128 = 1;
const BTRFS_FT_DIR: i128 = 2;
const BTRFS_FT_CHRDEV: i128 = 3;
const BTRFS_FT_BLKDEV: i128 = 4;
const BTRFS_FT_FIFO: i128 = 5;
const BTRFS_FT_SOCK: i128 = 6;
const BTRFS_FT_SYMLINK: i128 = 7;
const BTRFS_FT_XATTR: i128 = 8;
const BTRFS_FT_MAX: i128 = 9;
const BTRFS_FREE_SPACE_EXTENT: i128 = 1;
const BTRFS_FREE_SPACE_BITMAP: i128 = 2;
const BTRFS_HEADER_FLAG_WRITTEN: i128 = 1 << 0;
const BTRFS_HEADER_FLAG_RELOC: i128 = 1 << 1;
const BTRFS_SUPER_FLAG_ERROR: i128 = 1 << 2;
const BTRFS_SUPER_FLAG_SEEDING: i128 = 1 << 32;
const BTRFS_SUPER_FLAG_METADUMP: i128 = 1 << 33;
const BTRFS_SUPER_FLAG_METADUMP_V2: i128 = 1 << 34;
const BTRFS_SUPER_FLAG_CHANGING_FSID: i128 = 1 << 35;
const BTRFS_SUPER_FLAG_CHANGING_FSID_V2: i128 = 1 << 36;
const BTRFS_EXTENT_FLAG_DATA: i128 = 1 << 0;
const BTRFS_EXTENT_FLAG_TREE_BLOCK: i128 = 1 << 1;
const BTRFS_BLOCK_FLAG_F_BACKREF: i128 = 1 << 8;
const BTRFS_EXTENT_FLAG_SUPER: i128 = 1 << 48;
const BTRFS_ROOT_SUBVOL_RDONLY: i128 = 1 << 0;
const BTRFS_ROOT_SUBVOL_DEAD: i128 = 1 << 48;
const BTRFS_DEV_REPLACE_ITEM_CONT_READING_FROM_SRCDEV_MODE_ALWAYS: i128 = 0;
const BTRFS_DEV_REPLACE_ITEM_CONT_READING_FROM_SRCDEV_MODE_AVOID: i128 = 1;
const BTRFS_BLOCK_GROUP_DATA: i128 = 1 << 0;
const BTRFS_BLOCK_GROUP_SYSTEM: i128 = 1 << 1;
const BTRFS_BLOCK_GROUP_METADATA: i128 = 1 << 2;
const BTRFS_BLOCK_GROUP_RAID0: i128 = 1 << 3;
const BTRFS_BLOCK_GROUP_RAID1: i128 = 1 << 4;
const BTRFS_BLOCK_GROUP_DUP: i128 = 1 << 5;
const BTRFS_BLOCK_GROUP_RAID10: i128 = 1 << 6;
const BTRFS_BLOCK_GROUP_RAID5: i128 = 1 << 7;
const BTRFS_BLOCK_GROUP_RAID6: i128 = 1 << 8;
const BTRFS_BLOCK_GROUP_RAID1C3: i128 = 1 << 9;
const BTRFS_BLOCK_GROUP_RAID1C4: i128 = 1 << 10;
const BTRFS_BLOCK_GROUP_RESERVED: i128 = BTRFS_AVAIL_ALLOC_BIT_SINGLE | BTRFS_SPACE_INFO_GLOBAL_RSV;
const BTRFS_BLOCK_GROUP_TYPE_MASK: i128 =
    BTRFS_BLOCK_GROUP_DATA | BTRFS_BLOCK_GROUP_SYSTEM | BTRFS_BLOCK_GROUP_METADATA;
const BTRFS_BLOCK_GROUP_PROFILE_MASK: i128 = BTRFS_BLOCK_GROUP_RAID0
    | BTRFS_BLOCK_GROUP_RAID1
    | BTRFS_BLOCK_GROUP_RAID1C3
    | BTRFS_BLOCK_GROUP_RAID1C4
    | BTRFS_BLOCK_GROUP_RAID5
    | BTRFS_BLOCK_GROUP_RAID6
    | BTRFS_BLOCK_GROUP_DUP
    | BTRFS_BLOCK_GROUP_RAID10;
const BTRFS_BLOCK_GROUP_RAID56_MASK: i128 = BTRFS_BLOCK_GROUP_RAID5 | BTRFS_BLOCK_GROUP_RAID6;
const BTRFS_BLOCK_GROUP_RAID1_MASK: i128 =
    BTRFS_BLOCK_GROUP_RAID1 | BTRFS_BLOCK_GROUP_RAID1C3 | BTRFS_BLOCK_GROUP_RAID1C4;
const BTRFS_AVAIL_ALLOC_BIT_SINGLE: i128 = 1 << 48;
const BTRFS_SPACE_INFO_GLOBAL_RSV: i128 = 1 << 49;
const BTRFS_EXTENDED_PROFILE_MASK: i128 =
    BTRFS_BLOCK_GROUP_PROFILE_MASK | BTRFS_AVAIL_ALLOC_BIT_SINGLE;
const BTRFS_FREE_SPACE_USING_BITMAPS: i128 = 1 << 0;
const BTRFS_QGROUP_LEVEL_SHIFT: i128 = 48;
const BTRFS_QGROUP_STATUS_FLAG_ON: i128 = 1 << 0;
const BTRFS_QGROUP_STATUS_FLAG_RESCAN: i128 = 1 << 1;
const BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT: i128 = 1 << 2;
const BTRFS_QGROUP_STATUS_VERSION: i128 = 1;

macro_rules! constant {
    ($ident: ident) => {
        Constant {
            name: stringify!($ident),
            value: $ident.into(),
        }
    };
}

lazy_static! {
    pub static ref CONSTANTS: Vec<Constant> = vec![
        constant!(BTRFS_DEV_STAT_WRITE_ERRS),
        constant!(BTRFS_DEV_STAT_READ_ERRS),
        constant!(BTRFS_DEV_STAT_FLUSH_ERRS),
        constant!(BTRFS_DEV_STAT_CORRUPTION_ERRS),
        constant!(BTRFS_DEV_STAT_GENERATION_ERRS),
        constant!(BTRFS_DEV_STAT_VALUES_MAX),
        constant!(BTRFS_CSUM_TYPE_CRC32),
        constant!(BTRFS_CSUM_TYPE_XXHASH),
        constant!(BTRFS_CSUM_TYPE_SHA256),
        constant!(BTRFS_CSUM_TYPE_BLAKE2),
        constant!(BTRFS_FILE_EXTENT_INLINE),
        constant!(BTRFS_FILE_EXTENT_REG),
        constant!(BTRFS_FILE_EXTENT_PREALLOC),
        constant!(BTRFS_NR_FILE_EXTENT_TYPES),
        constant!(BTRFS_RAID_RAID10),
        constant!(BTRFS_RAID_RAID1),
        constant!(BTRFS_RAID_DUP),
        constant!(BTRFS_RAID_RAID0),
        constant!(BTRFS_RAID_SINGLE),
        constant!(BTRFS_RAID_RAID5),
        constant!(BTRFS_RAID_RAID6),
        constant!(BTRFS_RAID_RAID1C3),
        constant!(BTRFS_RAID_RAID1C4),
        constant!(BTRFS_NR_RAID_TYPES),
        constant!(BTRFS_UUID_SIZE),
        constant!(BTRFS_ROOT_TREE_OBJECTID),
        constant!(BTRFS_EXTENT_TREE_OBJECTID),
        constant!(BTRFS_CHUNK_TREE_OBJECTID),
        constant!(BTRFS_DEV_TREE_OBJECTID),
        constant!(BTRFS_FS_TREE_OBJECTID),
        constant!(BTRFS_ROOT_TREE_DIR_OBJECTID),
        constant!(BTRFS_CSUM_TREE_OBJECTID),
        constant!(BTRFS_QUOTA_TREE_OBJECTID),
        constant!(BTRFS_UUID_TREE_OBJECTID),
        constant!(BTRFS_FREE_SPACE_TREE_OBJECTID),
        constant!(BTRFS_DEV_STATS_OBJECTID),
        constant!(BTRFS_BALANCE_OBJECTID),
        constant!(BTRFS_ORPHAN_OBJECTID),
        constant!(BTRFS_TREE_LOG_OBJECTID),
        constant!(BTRFS_TREE_LOG_FIXUP_OBJECTID),
        constant!(BTRFS_TREE_RELOC_OBJECTID),
        constant!(BTRFS_DATA_RELOC_TREE_OBJECTID),
        constant!(BTRFS_EXTENT_CSUM_OBJECTID),
        constant!(BTRFS_FREE_SPACE_OBJECTID),
        constant!(BTRFS_FREE_INO_OBJECTID),
        constant!(BTRFS_MULTIPLE_OBJECTIDS),
        constant!(BTRFS_FIRST_FREE_OBJECTID),
        constant!(BTRFS_LAST_FREE_OBJECTID),
        constant!(BTRFS_FIRST_CHUNK_TREE_OBJECTID),
        constant!(BTRFS_DEV_ITEMS_OBJECTID),
        constant!(BTRFS_BTREE_INODE_OBJECTID),
        constant!(BTRFS_EMPTY_SUBVOL_DIR_OBJECTID),
        constant!(BTRFS_DEV_REPLACE_DEVID),
        constant!(BTRFS_INODE_ITEM_KEY),
        constant!(BTRFS_INODE_REF_KEY),
        constant!(BTRFS_INODE_EXTREF_KEY),
        constant!(BTRFS_XATTR_ITEM_KEY),
        constant!(BTRFS_ORPHAN_ITEM_KEY),
        constant!(BTRFS_DIR_LOG_ITEM_KEY),
        constant!(BTRFS_DIR_LOG_INDEX_KEY),
        constant!(BTRFS_DIR_ITEM_KEY),
        constant!(BTRFS_DIR_INDEX_KEY),
        constant!(BTRFS_EXTENT_DATA_KEY),
        constant!(BTRFS_EXTENT_CSUM_KEY),
        constant!(BTRFS_ROOT_ITEM_KEY),
        constant!(BTRFS_ROOT_BACKREF_KEY),
        constant!(BTRFS_ROOT_REF_KEY),
        constant!(BTRFS_EXTENT_ITEM_KEY),
        constant!(BTRFS_METADATA_ITEM_KEY),
        constant!(BTRFS_TREE_BLOCK_REF_KEY),
        constant!(BTRFS_EXTENT_DATA_REF_KEY),
        constant!(BTRFS_EXTENT_REF_V0_KEY),
        constant!(BTRFS_SHARED_BLOCK_REF_KEY),
        constant!(BTRFS_SHARED_DATA_REF_KEY),
        constant!(BTRFS_BLOCK_GROUP_ITEM_KEY),
        constant!(BTRFS_FREE_SPACE_INFO_KEY),
        constant!(BTRFS_FREE_SPACE_EXTENT_KEY),
        constant!(BTRFS_FREE_SPACE_BITMAP_KEY),
        constant!(BTRFS_DEV_EXTENT_KEY),
        constant!(BTRFS_DEV_ITEM_KEY),
        constant!(BTRFS_CHUNK_ITEM_KEY),
        constant!(BTRFS_QGROUP_STATUS_KEY),
        constant!(BTRFS_QGROUP_INFO_KEY),
        constant!(BTRFS_QGROUP_LIMIT_KEY),
        constant!(BTRFS_QGROUP_RELATION_KEY),
        constant!(BTRFS_BALANCE_ITEM_KEY),
        constant!(BTRFS_TEMPORARY_ITEM_KEY),
        constant!(BTRFS_DEV_STATS_KEY),
        constant!(BTRFS_PERSISTENT_ITEM_KEY),
        constant!(BTRFS_DEV_REPLACE_KEY),
        constant!(BTRFS_UUID_KEY_SUBVOL),
        constant!(BTRFS_UUID_KEY_RECEIVED_SUBVOL),
        constant!(BTRFS_STRING_ITEM_KEY),
        constant!(BTRFS_CSUM_SIZE),
        constant!(BTRFS_FT_UNKNOWN),
        constant!(BTRFS_FT_REG_FILE),
        constant!(BTRFS_FT_DIR),
        constant!(BTRFS_FT_CHRDEV),
        constant!(BTRFS_FT_BLKDEV),
        constant!(BTRFS_FT_FIFO),
        constant!(BTRFS_FT_SOCK),
        constant!(BTRFS_FT_SYMLINK),
        constant!(BTRFS_FT_XATTR),
        constant!(BTRFS_FT_MAX),
        constant!(BTRFS_FREE_SPACE_EXTENT),
        constant!(BTRFS_FREE_SPACE_BITMAP),
        constant!(BTRFS_HEADER_FLAG_WRITTEN),
        constant!(BTRFS_HEADER_FLAG_RELOC),
        constant!(BTRFS_SUPER_FLAG_ERROR),
        constant!(BTRFS_SUPER_FLAG_SEEDING),
        constant!(BTRFS_SUPER_FLAG_METADUMP),
        constant!(BTRFS_SUPER_FLAG_METADUMP_V2),
        constant!(BTRFS_SUPER_FLAG_CHANGING_FSID),
        constant!(BTRFS_SUPER_FLAG_CHANGING_FSID_V2),
        constant!(BTRFS_EXTENT_FLAG_DATA),
        constant!(BTRFS_EXTENT_FLAG_TREE_BLOCK),
        constant!(BTRFS_BLOCK_FLAG_F_BACKREF),
        constant!(BTRFS_EXTENT_FLAG_SUPER),
        constant!(BTRFS_ROOT_SUBVOL_RDONLY),
        constant!(BTRFS_ROOT_SUBVOL_DEAD),
        constant!(BTRFS_DEV_REPLACE_ITEM_CONT_READING_FROM_SRCDEV_MODE_ALWAYS),
        constant!(BTRFS_DEV_REPLACE_ITEM_CONT_READING_FROM_SRCDEV_MODE_AVOID),
        constant!(BTRFS_BLOCK_GROUP_DATA),
        constant!(BTRFS_BLOCK_GROUP_SYSTEM),
        constant!(BTRFS_BLOCK_GROUP_METADATA),
        constant!(BTRFS_BLOCK_GROUP_RAID0),
        constant!(BTRFS_BLOCK_GROUP_RAID1),
        constant!(BTRFS_BLOCK_GROUP_DUP),
        constant!(BTRFS_BLOCK_GROUP_RAID10),
        constant!(BTRFS_BLOCK_GROUP_RAID5),
        constant!(BTRFS_BLOCK_GROUP_RAID6),
        constant!(BTRFS_BLOCK_GROUP_RAID1C3),
        constant!(BTRFS_BLOCK_GROUP_RAID1C4),
        constant!(BTRFS_BLOCK_GROUP_RESERVED),
        constant!(BTRFS_BLOCK_GROUP_TYPE_MASK),
        constant!(BTRFS_BLOCK_GROUP_PROFILE_MASK),
        constant!(BTRFS_BLOCK_GROUP_RAID56_MASK),
        constant!(BTRFS_BLOCK_GROUP_RAID1_MASK),
        constant!(BTRFS_AVAIL_ALLOC_BIT_SINGLE),
        constant!(BTRFS_SPACE_INFO_GLOBAL_RSV),
        constant!(BTRFS_EXTENDED_PROFILE_MASK),
        constant!(BTRFS_FREE_SPACE_USING_BITMAPS),
        constant!(BTRFS_QGROUP_LEVEL_SHIFT),
        constant!(BTRFS_QGROUP_STATUS_FLAG_ON),
        constant!(BTRFS_QGROUP_STATUS_FLAG_RESCAN),
        constant!(BTRFS_QGROUP_STATUS_FLAG_INCONSISTENT),
        constant!(BTRFS_QGROUP_STATUS_VERSION),
    ];
    static ref BTRFS_STRIPE: Struct = Struct {
        name: "btrfs_stripe",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("devid"),
                ty: Type::U64,
            },
            Field {
                name: Some("offset"),
                ty: Type::U64,
            },
            Field {
                name: Some("dev_uuid"),
                ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
            },
        ],
    };
    pub static ref BTRFS_SEARCH_KEY: Struct = Struct {
        name: "_btrfs_ioctl_search_key",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("min_objectid"),
                ty: Type::U64,
            },
            Field {
                name: Some("max_objectid"),
                ty: Type::U64,
            },
            Field {
                name: Some("min_type"),
                ty: Type::U8,
            },
            Field {
                name: Some("max_type"),
                ty: Type::U8,
            },
            Field {
                name: Some("min_offset"),
                ty: Type::U64,
            },
            Field {
                name: Some("max_offset"),
                ty: Type::U64,
            },
            Field {
                name: Some("min_transid"),
                ty: Type::U64,
            },
            Field {
                name: Some("max_transid"),
                ty: Type::U64,
            },
        ],
    };
    pub static ref BTRFS_KEY: Struct = Struct {
        name: "btrfs_key",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("objectid"),
                ty: Type::U64,
            },
            Field {
                name: Some("type"),
                ty: Type::U8,
            },
            Field {
                name: Some("offset"),
                ty: Type::U64,
            },
        ],
    };
    static ref BTRFS_TIMESPEC: Struct = Struct {
        name: "btrfs_timespec",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("sec"),
                ty: Type::U64,
            },
            Field {
                name: Some("nsec"),
                ty: Type::U32,
            },
        ],
    };
    static ref BTRFS_INODE_ITEM: Struct = Struct {
        name: "btrfs_inode_item",
        key_match: |_, ty, off| ty == BTRFS_INODE_ITEM_KEY && off == 0,
        fields: vec![
            Field {
                name: Some("generation"),
                ty: Type::U64,
            },
            Field {
                name: Some("transid"),
                ty: Type::U64,
            },
            Field {
                name: Some("size"),
                ty: Type::U64,
            },
            Field {
                name: Some("nbytes"),
                ty: Type::U64,
            },
            Field {
                name: Some("block_group"),
                ty: Type::U64,
            },
            Field {
                name: Some("nlink"),
                ty: Type::U32,
            },
            Field {
                name: Some("uid"),
                ty: Type::U32,
            },
            Field {
                name: Some("gid"),
                ty: Type::U32,
            },
            Field {
                name: Some("mode"),
                ty: Type::U32,
            },
            Field {
                name: Some("rdev"),
                ty: Type::U64,
            },
            Field {
                name: Some("flags"),
                ty: Type::U64,
            },
            Field {
                name: Some("sequence"),
                ty: Type::U64,
            },
            Field {
                name: Some("reserved"),
                ty: Type::Array(Box::new(Type::U64), 4),
            },
            Field {
                name: Some("atime"),
                ty: Type::Struct(BTRFS_TIMESPEC.clone()),
            },
            Field {
                name: Some("ctime"),
                ty: Type::Struct(BTRFS_TIMESPEC.clone()),
            },
            Field {
                name: Some("mtime"),
                ty: Type::Struct(BTRFS_TIMESPEC.clone()),
            },
            Field {
                name: Some("otime"),
                ty: Type::Struct(BTRFS_TIMESPEC.clone()),
            },
        ],
    };
    static ref ANON_STRUCT_0_BTRFS_DISK_BALANCE_ARGS: Struct = Struct {
        name: "_anon_struct_0_btrfs_disk_balance_args",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("usage_min"),
                ty: Type::U32,
            },
            Field {
                name: Some("usage_max"),
                ty: Type::U32,
            },
        ],
    };
    static ref ANON_STRUCT_1_BTRFS_DISK_BALANCE_ARGS: Struct = Struct {
        name: "_anon_struct_1_btrfs_disk_balance_args",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("limit_min"),
                ty: Type::U32,
            },
            Field {
                name: Some("limit_max"),
                ty: Type::U32,
            },
        ],
    };
    static ref BTRFS_DISK_BALANCE_ARGS: Struct = Struct {
        name: "btrfs_disk_balance_args",
        key_match: |_, _, _| false,
        fields: vec![
            Field {
                name: Some("profiles"),
                ty: Type::U64,
            },
            Field {
                name: None,
                ty: Type::Union(Union {
                    name: "_anon_union_0_btrfs_disk_balance_args",
                    fields: vec![
                        Field {
                            name: Some("usage"),
                            ty: Type::U64,
                        },
                        Field {
                            name: None,
                            ty: Type::Struct(ANON_STRUCT_0_BTRFS_DISK_BALANCE_ARGS.clone())
                        },
                    ],
                })
            },
            Field {
                name: Some("devid"),
                ty: Type::U64,
            },
            Field {
                name: Some("pstart"),
                ty: Type::U64,
            },
            Field {
                name: Some("pend"),
                ty: Type::U64,
            },
            Field {
                name: Some("vstart"),
                ty: Type::U64,
            },
            Field {
                name: Some("vend"),
                ty: Type::U64,
            },
            Field {
                name: Some("target"),
                ty: Type::U64,
            },
            Field {
                name: Some("flags"),
                ty: Type::U64,
            },
            Field {
                name: None,
                ty: Type::Union(Union {
                    name: "_anon_union_1_btrfs_disk_balance_args",
                    fields: vec![
                        Field {
                            name: Some("limit"),
                            ty: Type::U64,
                        },
                        Field {
                            name: None,
                            ty: Type::Struct(ANON_STRUCT_1_BTRFS_DISK_BALANCE_ARGS.clone())
                        },
                    ],
                })
            },
            Field {
                name: Some("stripes_min"),
                ty: Type::U32,
            },
            Field {
                name: Some("stripes_max"),
                ty: Type::U32,
            },
            Field {
                name: Some("unused"),
                ty: Type::Array(Box::new(Type::U64), 6),
            },
        ],
    };
    pub static ref STRUCTS: Vec<Struct> = vec![
        BTRFS_SEARCH_KEY.clone(),
        BTRFS_KEY.clone(),
        Struct {
            name: "btrfs_dev_item",
            key_match: |o, ty, _| o == BTRFS_DEV_ITEMS_OBJECTID && ty == BTRFS_DEV_ITEM_KEY,
            fields: vec![
                Field {
                    name: Some("devid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("total_bytes"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("bytes_used"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("io_align"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("io_width"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("sector_size"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("type"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("start_offset"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("dev_group"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("seek_speed"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("bandwidth"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("uuid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
                Field {
                    name: Some("fsid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
            ],
        },
        BTRFS_STRIPE.clone(),
        Struct {
            name: "btrfs_chunk",
            key_match: |o, ty, _| o == BTRFS_FIRST_CHUNK_TREE_OBJECTID
                && ty == BTRFS_CHUNK_ITEM_KEY,
            fields: vec![
                Field {
                    name: Some("length"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("owner"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("stripe_len"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("type"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("io_align"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("io_width"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("sector_size"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("num_stripes"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("sub_stripes"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("stripes"),
                    ty: Type::TrailingTypes(
                        Box::new(Type::Struct(BTRFS_STRIPE.clone())),
                        "num_stripes",
                    ),
                },
            ],
        },
        Struct {
            name: "btrfs_extent_item",
            key_match: |_, ty, _| ty == BTRFS_EXTENT_ITEM_KEY || ty == BTRFS_METADATA_ITEM_KEY,
            fields: vec![Field {
                name: None,
                ty: Type::DynamicStruct(|_bytes| -> Result<Vec<Field>> {
                    unimplemented!();
                }),
            },],
        },
        Struct {
            name: "btrfs_dev_extent",
            key_match: |_, ty, _| ty == BTRFS_DEV_EXTENT_KEY,
            fields: vec![
                Field {
                    name: Some("chunk_tree"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("chunk_objectid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("chunk_offset"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("length"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("chunk_tree_uuid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
            ],
        },
        Struct {
            name: "btrfs_inode_ref",
            key_match: |_, ty, _| ty == BTRFS_INODE_REF_KEY,
            fields: vec![
                Field {
                    name: Some("index"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("name_len"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("name"),
                    ty: Type::TrailingString("name_len"),
                },
            ],
        },
        Struct {
            name: "btrfs_inode_extref",
            key_match: |_, ty, _| ty == BTRFS_INODE_EXTREF_KEY,
            fields: vec![
                Field {
                    name: Some("parent_objectid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("index"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("name_len"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("name"),
                    ty: Type::TrailingString("name_len"),
                },
            ],
        },
        BTRFS_TIMESPEC.clone(),
        BTRFS_INODE_ITEM.clone(),
        Struct {
            name: "btrfs_dir_log_item",
            key_match: |_, ty, _| ty == BTRFS_INODE_EXTREF_KEY || ty == BTRFS_DIR_LOG_INDEX_KEY,
            fields: vec![Field {
                name: Some("end"),
                ty: Type::U64,
            },],
        },
        Struct {
            name: "btrfs_dir_item",
            key_match: |_, ty, _| ty == BTRFS_DIR_ITEM_KEY || ty == BTRFS_XATTR_ITEM_KEY,
            fields: vec![
                Field {
                    name: Some("location"),
                    ty: Type::Struct(BTRFS_KEY.clone()),
                },
                Field {
                    name: Some("transid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("data_len"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("name_len"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("type"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("name"),
                    ty: Type::TrailingString("name_len"),
                },
                Field {
                    name: Some("value"),
                    ty: Type::TrailingString("data_len"),
                },
            ],
        },
        Struct {
            name: "btrfs_root_item",
            key_match: |_, ty, _| ty == BTRFS_ROOT_ITEM_KEY,
            fields: vec![
                Field {
                    name: Some("inode"),
                    ty: Type::Struct(BTRFS_INODE_ITEM.clone()),
                },
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("root_dirid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("bytenr"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("byte_limit"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("bytes_used"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("last_snapshot"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("flags"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("refs"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("drop_progress"),
                    ty: Type::Struct(BTRFS_KEY.clone()),
                },
                Field {
                    name: Some("drop_level"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("level"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("generation_v2"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("uuid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
                Field {
                    name: Some("parent_uuid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
                Field {
                    name: Some("received_uuid"),
                    ty: Type::Array(Box::new(Type::U8), BTRFS_UUID_SIZE.into()),
                },
                Field {
                    name: Some("ctransid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("otransid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("stransid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rtransid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("ctime"),
                    ty: Type::Struct(BTRFS_TIMESPEC.clone()),
                },
                Field {
                    name: Some("otime"),
                    ty: Type::Struct(BTRFS_TIMESPEC.clone()),
                },
                Field {
                    name: Some("stime"),
                    ty: Type::Struct(BTRFS_TIMESPEC.clone()),
                },
                Field {
                    name: Some("rtime"),
                    ty: Type::Struct(BTRFS_TIMESPEC.clone()),
                },
                Field {
                    name: Some("reserved"),
                    ty: Type::Array(Box::new(Type::U64), 8),
                },
            ],
        },
        Struct {
            name: "btrfs_roof_ref",
            key_match: |_, ty, _| ty == BTRFS_ROOT_REF_KEY || ty == BTRFS_ROOT_BACKREF_KEY,
            fields: vec![
                Field {
                    name: Some("dirid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("sequence"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("name_len"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("name"),
                    ty: Type::TrailingString("name_len"),
                },
            ],
        },
        ANON_STRUCT_0_BTRFS_DISK_BALANCE_ARGS.clone(),
        ANON_STRUCT_1_BTRFS_DISK_BALANCE_ARGS.clone(),
        BTRFS_DISK_BALANCE_ARGS.clone(),
        Struct {
            name: "btrfs_balance_item",
            key_match: |oid, ty, off| oid == BTRFS_BALANCE_OBJECTID
                && ty == BTRFS_TEMPORARY_ITEM_KEY
                && off == 0,
            fields: vec![
                Field {
                    name: Some("flags"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("data"),
                    ty: Type::Struct(BTRFS_DISK_BALANCE_ARGS.clone()),
                },
                Field {
                    name: Some("meta"),
                    ty: Type::Struct(BTRFS_DISK_BALANCE_ARGS.clone()),
                },
                Field {
                    name: Some("sys"),
                    ty: Type::Struct(BTRFS_DISK_BALANCE_ARGS.clone()),
                },
            ],
        },
        Struct {
            name: "btrfs_file_extent_item",
            key_match: |_, ty, _| ty == BTRFS_EXTENT_DATA_KEY,
            fields: vec![
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("ram_bytes"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("compression"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("encryption"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("other_encoding"),
                    ty: Type::U16,
                },
                Field {
                    name: Some("type"),
                    ty: Type::U8,
                },
                Field {
                    name: Some("disk_bytenr"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("disk_num_bytes"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("offset"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("num_bytes"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_csum_item",
            key_match: |oid, ty, _| oid == BTRFS_EXTENT_CSUM_OBJECTID.into()
                && ty == BTRFS_EXTENT_CSUM_KEY,
            fields: vec![Field {
                name: Some("csum"),
                ty: Type::U8,
            },],
        },
        Struct {
            name: "btrfs_dev_stats_item",
            key_match: |oid, ty, _| oid == BTRFS_DEV_STATS_OBJECTID
                && ty == BTRFS_PERSISTENT_ITEM_KEY,
            fields: vec![Field {
                name: Some("values"),
                ty: Type::Array(Box::new(Type::U64), BTRFS_DEV_STAT_VALUES_MAX.into()),
            },],
        },
        Struct {
            name: "btrfs_dev_replace_item",
            key_match: |_, ty, _| ty == BTRFS_DEV_REPLACE_KEY,
            fields: vec![
                Field {
                    name: Some("src_devid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("cursor_left"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("cursor_right"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("cont_reading_from_srcdev_mode"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("replace_state"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("time_started"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("time_stopped"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("num_write_errors"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("num_uncorrectable_read_errors"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_block_group_item",
            key_match: |_, ty, _| ty == BTRFS_BLOCK_GROUP_ITEM_KEY,
            fields: vec![
                Field {
                    name: Some("used"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("chunk_objectid"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("flags"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_free_space_info",
            key_match: |_, ty, _| ty == BTRFS_FREE_SPACE_INFO_KEY,
            fields: vec![
                Field {
                    name: Some("extent_count"),
                    ty: Type::U32,
                },
                Field {
                    name: Some("flags"),
                    ty: Type::U32,
                },
            ],
        },
        Struct {
            name: "btrfs_free_space_header",
            key_match: |oid, ty, _| oid == BTRFS_FREE_SPACE_OBJECTID.into() && ty == 0,
            fields: vec![
                Field {
                    name: Some("location"),
                    ty: Type::Struct(BTRFS_KEY.clone()),
                },
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("num_entries"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("num_bitmaps"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_qgroup_status_item",
            key_match: |oid, ty, off| oid == 0 && ty == BTRFS_QGROUP_STATUS_KEY && off == 0,
            fields: vec![
                Field {
                    name: Some("version"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("flags"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rescan"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_qgroup_info_item",
            key_match: |oid, ty, _| oid == 0 && ty == BTRFS_QGROUP_INFO_KEY,
            fields: vec![
                Field {
                    name: Some("generation"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rfer"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rfer_cmpr"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("excl"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("excl_cmpr"),
                    ty: Type::U64,
                },
            ],
        },
        Struct {
            name: "btrfs_qgroup_limit_item",
            key_match: |oid, ty, _| oid == 0 && ty == BTRFS_QGROUP_LIMIT_KEY,
            fields: vec![
                Field {
                    name: Some("flags"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("max_rfer"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("max_excl"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rsv_rfer"),
                    ty: Type::U64,
                },
                Field {
                    name: Some("rsv_excl"),
                    ty: Type::U64,
                },
            ],
        },
    ];
}

#[cfg(test)]
mod test {
    use super::{CONSTANTS, STRUCTS};
    use crate::btrfs::structs::{Field, Type};
    use std::collections::HashSet;

    #[test]
    fn test_constant_names_unique() {
        let mut set = HashSet::new();
        for constant in &*CONSTANTS {
            assert!(!set.contains(constant.name));
            set.insert(constant.name);
        }
    }

    #[test]
    fn test_struct_field_names_unique() {
        fn recurse_fields(set: &mut HashSet<&'static str>, fields: &[Field]) {
            for field in fields {
                if let Some(name) = field.name {
                    assert!(!set.contains(name));
                    set.insert(name);
                } else {
                    match &field.ty {
                        Type::Struct(s) => recurse_fields(set, &s.fields),
                        Type::Union(u) => recurse_fields(set, &u.fields),
                        Type::DynamicStruct(_) => (),
                        _ => assert!(false, "Non struct/union anon field"),
                    }
                }
            }
        }

        for s in &*STRUCTS {
            let mut set = HashSet::new();
            recurse_fields(&mut set, &s.fields);
        }
    }

    #[test]
    fn test_struct_names_unique() {
        let mut set = HashSet::new();
        for s in &*STRUCTS {
            assert!(!set.contains(s.name));
            set.insert(s.name);
        }
    }

    #[test]
    fn test_only_anon_struct_unions_or_dynamicstruct() {
        for s in &*STRUCTS {
            for field in &s.fields {
                if field.name.is_none() {
                    match field.ty {
                        Type::Struct(_) | Type::Union(_) | Type::DynamicStruct(_) => (),
                        _ => assert!(
                            false,
                            "Anonymous field is not struct, union or dynamic struct"
                        ),
                    }
                }
            }
        }
    }

    #[test]
    fn test_trailing_fields_exist() {
        for s in &*STRUCTS {
            for field in &s.fields {
                match field.ty {
                    Type::TrailingString(len_field) | Type::TrailingTypes(_, len_field) => {
                        assert!(s.fields.iter().any(|f| {
                            f.name.map_or(false, |n| n == len_field)
                                && (match f.ty {
                                    Type::U8 | Type::U16 | Type::U32 | Type::U64 => true,
                                    _ => false,
                                })
                        }));
                    }
                    _ => (),
                };
            }
        }
    }
}
