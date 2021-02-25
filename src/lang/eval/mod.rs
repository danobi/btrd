#[allow(clippy::module_inception)]
pub mod eval;
mod value;

pub use eval::{Eval, EvalResult};
