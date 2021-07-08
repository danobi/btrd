use std::alloc::{alloc_zeroed, Layout};
use std::collections::BTreeSet;
use std::convert::TryInto;
use std::fs::{File, OpenOptions};
use std::mem::size_of;
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::slice::SliceIndex;

use anyhow::{anyhow, bail, ensure, Result};
use log::info;
use memmap2::MmapMut;
use nix::dir::Dir;
use nix::errno::Errno;
use nix::fcntl::OFlag;
use nix::ioctl_readwrite;
use nix::sys::{stat::Mode, statfs::fstatfs};
use nix::Error as NixError;

const BTRFS_SUPERBLOCK_MAGIC: [u8; 8] = *b"_BHRfS_M";
const BTRFS_SUPERBLOCK_MAGIC_LOCS: [usize; 3] =
    [0x1_0000 + 0x40, 0x400_0000 + 0x40, 0x40_0000_0000 + 0x40];
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
#[derive(Default, Debug)]
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BtrfsIoctlSearchHeader {
    pub transid: u64,
    pub objectid: u64,
    pub offset: u64,
    pub ty: u32,
    pub len: u32,
}

enum FsInner {
    Mounted(Dir),
    Unmounted(MmapMut),
}

/// Main struct for interacting with btrfs filesystem
///
/// Holds a refcount on the FS while alive and decrements when struct is dropped (to prevent FS
/// from being unmounted while we're debugging)
pub struct Fs {
    inner: FsInner,
}

impl Fs {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        if let Ok(d) = Dir::open(
            path.as_ref(),
            OFlag::O_DIRECTORY | OFlag::O_RDONLY,
            Mode::empty(),
        ) {
            Self::new_mounted(d, path)
        } else if let Ok(f) = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path.as_ref())
        {
            Self::new_unmounted(f, path)
        } else {
            bail!(
                "{} is neither a mounted nor unmounted btrfs filesystem",
                path.as_ref().display()
            );
        }
    }

    fn new_mounted<P: AsRef<Path>>(fs: Dir, path: P) -> Result<Self> {
        let statfs = fstatfs(&fs)?;
        ensure!(
            i64::from(statfs.filesystem_type().0) == BTRFS_FSTYPE,
            "{} is not a btrfs filesystem",
            path.as_ref().display()
        );

        Ok(Self {
            inner: FsInner::Mounted(fs),
        })
    }

    fn has_superblock_magic(fs: &[u8]) -> bool {
        for loc in &BTRFS_SUPERBLOCK_MAGIC_LOCS {
            if let Some(magic) = fs.get(*loc..(loc + 8)) {
                if magic == BTRFS_SUPERBLOCK_MAGIC {
                    return true;
                }
            }
        }

        false
    }

    fn new_unmounted<P: AsRef<Path>>(fs: File, path: P) -> Result<Self> {
        let mmap = unsafe { MmapMut::map_mut(&fs) }?;

        ensure!(
            Self::has_superblock_magic(&*mmap),
            "Failed to find valid superblock magic for: {}",
            path.as_ref().display(),
        );

        Ok(Self {
            inner: FsInner::Unmounted(mmap),
        })
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
        min_transid: u64,
        max_transid: u64,
    ) -> Result<Vec<(BtrfsIoctlSearchHeader, Vec<u8>)>> {
        let fs = match &self.inner {
            FsInner::Mounted(fs) => fs,
            FsInner::Unmounted(_) => bail!("Cannot search() an unmounted filesystem"),
        };
        let retry = max_objectid != u64::MAX
            || max_type != u8::MAX
            || max_offset != u64::MAX
            || max_transid != u64::MAX;
        let mut ret = Vec::new();
        let mut seen = BTreeSet::new();
        let mut collisions = 0;

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

            match unsafe { btrfs_tree_search_v2(fs.as_raw_fd(), &mut *args) } {
                Ok(_) => (),
                Err(NixError::Sys(Errno::EOVERFLOW)) => (),
                Err(e) => bail!(e),
            };

            info!("search() key: {:#?}", args.key);
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

                if seen.contains(&header) {
                    collisions += 1;
                } else {
                    seen.insert(header.clone());
                    ret.push((header, bytes));
                }
            }

            if !retry || args.key.nr_items == 0 {
                break;
            }

            // Find the largest key in the values we've seen
            let largest = ret
                .iter()
                .map(|(header, _)| header)
                .max_by(|lhs, rhs| {
                    use std::cmp::Ordering;

                    if lhs.objectid < rhs.objectid {
                        Ordering::Less
                    } else if lhs.objectid > rhs.objectid {
                        Ordering::Greater
                    } else if lhs.ty < rhs.ty {
                        Ordering::Less
                    } else if lhs.ty > rhs.ty {
                        Ordering::Greater
                    } else if lhs.offset < rhs.offset {
                        Ordering::Less
                    } else if lhs.offset > rhs.offset {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                })
                .unwrap(); // Should have already returned if empty

            min_objectid = largest.objectid;
            min_type = largest.ty.try_into()?;
            min_offset = largest
                .offset
                .checked_add(1)
                .ok_or_else(|| anyhow!("Could not bump key.offset -- overflow detected"))?;
        }

        if collisions != 0 {
            bail!(
                "Saw {} identical payloads -- this should not be possible",
                collisions
            );
        }

        Ok(ret)
    }

    pub fn get_bytes<I>(&self, index: I) -> Result<&I::Output>
    where
        I: SliceIndex<[u8]> + std::fmt::Debug,
    {
        match &self.inner {
            FsInner::Unmounted(fs) => fs
                .get(index)
                .ok_or_else(|| anyhow!("Index out of range, max length is {}", fs.len())),
            FsInner::Mounted(_) => bail!("Cannot reinterpret bytes from mounted image"),
        }
    }
}
