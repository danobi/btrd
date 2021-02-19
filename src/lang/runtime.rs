use std::io::Write;

use crate::lang::eval::{Eval, EvalResult};
use crate::lang::parse::parse;
use crate::lang::semantics::SemanticAnalyzer;

pub struct Runtime<'a> {
    semantics: SemanticAnalyzer,
    eval: Eval<'a>,
}

impl<'a> Runtime<'a> {
    /// Create a new `Runtime` instance
    ///
    /// `sink` is where output should be written. eg. result of `print` statements
    ///
    /// `interactive` sets whether or not expression statements should print the result (useful
    /// when human is at a REPL)
    pub fn new(sink: &'a mut dyn Write, interactive: bool) -> Self {
        let semantics = SemanticAnalyzer::new();
        let eval = Eval::new(sink, interactive);

        Self { semantics, eval }
    }

    pub fn eval(&mut self, cmd: &str) -> EvalResult {
        // Parse input into AST
        let stmts = match parse(cmd) {
            Ok(s) => s,
            Err(e) => return EvalResult::Err(e.to_string()),
        };

        // Perform semantic analysis
        match self.semantics.analyze(&stmts, &self.eval) {
            Ok(_) => (),
            Err(e) => return EvalResult::Err(e.to_string()),
        };

        // Evaluate AST
        self.eval.eval(&stmts)
    }
}
