// Dummy library, so btrd can be registered as a dependency in tools like
// https://github.com/facebookincubator/reindeer and so we can add docs to docs.rs.
pub mod btrfs;

#[doc(hidden)]
pub fn foo() {}
