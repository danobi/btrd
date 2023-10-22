use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Completer, Helper, Highlighter, Hinter, Result};

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
        if ctx.input().ends_with('\\') {
            Ok(ValidationResult::Incomplete)
        } else {
            Ok(ValidationResult::Valid(None))
        }
    }
}

pub fn strip_comments(input: &str) -> String {
    let mut stripped = String::with_capacity(input.len());
    for line in input.lines() {
        let mut in_string = false;
        for c in line.chars() {
            if c == '"' {
                in_string = !in_string;
            } else if c == '#' && !in_string {
                // Rest of the line is a comment
                break;
            }

            stripped.push(c);
        }

        // Replace newlines with spaces (it doesn't matter)
        stripped.push(' ');
    }

    // Remove extra newline
    stripped.pop();

    stripped
}

/// Fixup input so the parser is happy
///
/// Currently does two things:
/// * Remove the multiline escape created by `ReplHelper`
/// * Appends a `;` if not already present so the parser recognizes the input as a statement
pub fn fixup_input(input: &str) -> String {
    let mut ret = input.replace("\\\n", " ");
    if !ret.trim_end().ends_with(';') {
        ret += ";";
    }

    ret
}

#[test]
fn test_strip_comments() {
    let data = vec![
        (r#"asdf"#, r#"asdf"#),
        (r#"asdf #comment"#, r#"asdf "#),
        (r#"asdf#comment"#, r#"asdf"#),
        (r#""string#notcomment""#, r#""string#notcomment""#),
        (r#""string\#notcomment""#, r#""string\#notcomment""#),
    ];

    for (input, expected) in data {
        assert_eq!(strip_comments(input), expected);
    }
}

#[test]
fn test_fixup_input() {
    assert_eq!(fixup_input("asdf \\\nme"), "asdf  me;");
    assert_eq!(fixup_input("asdf \\ \nme"), "asdf \\ \nme;");
    assert_eq!(fixup_input("asdf \\ \nme;"), "asdf \\ \nme;");
    assert_eq!(fixup_input("meline"), "meline;");
    assert_eq!(fixup_input("meline;"), "meline;");
    assert_eq!(fixup_input("meline ;  "), "meline ;  ");
}
