use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::Result;
use rustyline_derive::{Completer, Helper, Highlighter, Hinter};

/// Helper that extends editor
///
/// Currently only implements `Validator` trait to trigger multiline editing when a `\` is seen at
/// the end of a line.
#[derive(Completer, Helper, Highlighter, Hinter)]
pub struct ReplHelper {}

impl ReplHelper {
    pub fn new() -> Self {
        ReplHelper {}
    }
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> Result<ValidationResult> {
        if ctx.input().trim_end().ends_with('\\') {
            Ok(ValidationResult::Incomplete)
        } else {
            Ok(ValidationResult::Valid(None))
        }
    }
}
