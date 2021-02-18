use std::path::Path;

use anyhow::{ensure, Result};
use nix::dir::Dir;
use nix::fcntl::OFlag;
use nix::sys::{stat::Mode, statfs::fstatfs};

const BTRFS_FSTYPE: i64 = 0x9123683e;

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
}
