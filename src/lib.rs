// Dummy library, so libbpf-cargo can be registered as a dependency in tools like
// https://github.com/facebookincubator/reindeer and so we can add docs to docs.rs.

#[doc(hidden)]
pub fn foo() {}
