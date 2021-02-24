use std::alloc::{alloc_zeroed, Layout};
use std::convert::TryInto;
use std::mem::size_of;
use std::os::unix::io::AsRawFd;
use std::path::Path;

use anyhow::{bail, ensure, Result};
use log::info;
use nix::dir::Dir;
use nix::errno::Errno;
use nix::fcntl::OFlag;
use nix::ioctl_readwrite;
use nix::sys::{stat::Mode, statfs::fstatfs};
use nix::Error as NixError;

const BTRFS_FSTYPE: i64 = 0x9123683e;
const BTRFS_IOC_MAGIC: usize = 0x94;
const MAX_BUF_SIZE: usize = 16 << 20; // 16 MB

ioctl_readwrite!(
    btrfs_tree_search_v2,
    BTRFS_IOC_MAGIC,
    17,
    BtrfsIoctlSearchArgsV2
);

#[repr(C)]
#[derive(Default)]
struct BtrfsIoctlSearchKey {
    tree_id: u64,
    min_objectid: u64,
    max_objectid: u64,
    min_offset: u64,
    max_offset: u64,
    min_transid: u64,
    max_transid: u64,
    min_type: u32,
    max_type: u32,
    /// In/out
    nr_items: u32,
    _unused: u32,
    _unused1: u64,
    _unused2: u64,
    _unused3: u64,
    _unused4: u64,
}

#[repr(C)]
pub struct BtrfsIoctlSearchArgsV2 {
    key: BtrfsIoctlSearchKey,
    buf_size: u64,
    buf: [u8; MAX_BUF_SIZE],
}

impl BtrfsIoctlSearchArgsV2 {
    /// Allocates on the heap so we don't blow the stack with our huge buffer
    fn new() -> Box<Self> {
        let mut args: Box<Self> = unsafe {
            // NB: Careful that we use the global allocator with proper type layout
            let ptr = alloc_zeroed(Layout::new::<Self>());
            Box::from_raw(ptr as _)
        };

        args.key = BtrfsIoctlSearchKey::default();
        args.key.nr_items = u32::MAX;
        args.buf_size = MAX_BUF_SIZE.try_into().unwrap();

        args
    }
}

#[repr(C)]
#[derive(Clone)]
pub struct BtrfsIoctlSearchHeader {
    pub transid: u64,
    pub objectid: u64,
    pub offset: u64,
    pub ty: u32,
    pub len: u32,
}

/// Main struct for interacting with btrfs filesystem
///
/// Holds a refcount on the FS while alive and decrements when struct is dropped (to prevent FS
/// from being unmounted while we're debugging)
pub struct Fs {
    fs: Dir,
}

impl Fs {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let fs = Dir::open(
            path.as_ref(),
            OFlag::O_DIRECTORY | OFlag::O_RDONLY,
            Mode::empty(),
        )?;

        let statfs = fstatfs(&fs)?;
        ensure!(
            statfs.filesystem_type().0 == BTRFS_FSTYPE,
            "{} is not a btrfs filesystem",
            path.as_ref().display()
        );

        Ok(Self { fs })
    }

    /// Issues search v2 ioctl with given parameters
    ///
    /// Returns pairs of (header, bytes)
    #[allow(clippy::too_many_arguments)]
    pub fn search(
        &self,
        tree_id: u64,
        mut min_objectid: u64,
        max_objectid: u64,
        mut min_type: u8,
        max_type: u8,
        mut min_offset: u64,
        max_offset: u64,
        mut min_transid: u64,
        max_transid: u64,
    ) -> Result<Vec<(BtrfsIoctlSearchHeader, Vec<u8>)>> {
        let retry = max_objectid != u64::MAX
            || max_type != u8::MAX
            || max_offset != u64::MAX
            || max_transid != u64::MAX;
        let mut ret = Vec::new();

        loop {
            let mut args = BtrfsIoctlSearchArgsV2::new();
            args.key.tree_id = tree_id;
            args.key.min_objectid = min_objectid;
            args.key.max_objectid = max_objectid;
            args.key.min_type = min_type.into();
            args.key.max_type = max_type.into();
            args.key.min_offset = min_offset;
            args.key.max_offset = max_offset;
            args.key.min_transid = min_transid;
            args.key.max_transid = max_transid;

            match unsafe { btrfs_tree_search_v2(self.fs.as_raw_fd(), &mut *args) } {
                Ok(_) => (),
                Err(NixError::Sys(Errno::EOVERFLOW)) => (),
                Err(e) => bail!(e),
            };

            info!("search() found {} items", args.key.nr_items);

            // Extract all the data from this ioctl
            let mut offset: usize = 0;
            for _ in 0..args.key.nr_items {
                // Extract header
                let header_sz = size_of::<BtrfsIoctlSearchHeader>();
                ensure!(
                    header_sz + offset <= MAX_BUF_SIZE,
                    "BtrfsIoctlSearchHeader short read"
                );
                let header = unsafe {
                    (&*(args.buf[offset..].as_ptr() as *const BtrfsIoctlSearchHeader)).clone()
                };
                offset += header_sz;

                // Extract associated payload
                ensure!(
                    header.len as usize + offset <= MAX_BUF_SIZE,
                    "BtrfsIoctlSearchHeader payload short read"
                );
                let bytes = args.buf[offset..(offset + header.len as usize)].to_vec();
                offset += header.len as usize;

                ret.push((header, bytes));
            }

            if !retry || args.key.nr_items == 0 {
                break;
            }

            // Reset the keys to continue the search
            if max_objectid != u64::MAX {
                min_objectid = ret
                    .iter()
                    .map(|(h, _)| h.objectid)
                    .max()
                    .unwrap() // Should have already returned if empty
                    + 1;
            }
            if max_type != u8::MAX {
                min_type = (ret
                    .iter()
                    .map(|(h, _)| h.ty)
                    .max()
                    .unwrap() // Should have already returned if empty
                    + 1)
                .try_into()?;
            }
            if max_offset != u64::MAX {
                min_offset = ret
                    .iter()
                    .map(|(h, _)| h.offset)
                    .max()
                    .unwrap() // Should have already returned if empty
                    + 1;
            }
            if max_transid != u64::MAX {
                min_transid = ret
                    .iter()
                    .map(|(h, _)| h.transid)
                    .max()
                    .unwrap() // Should have already returned if empty
                    + 1;
            }
        }

        Ok(ret)
    }
}
