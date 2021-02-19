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

        // HACK: run semantic analysis and eval in lockstep, statement by statement.
        //
        // The reason we do this is b/c btrd is a statically typed language. However, the
        // `search()` builtin's return type changes depending on the key used. The enable this type
        // magic, we need to evaluate `key()`'s arguments and detemine the matching on-disk struct.
        // And for evaluation to work correctly with variables, semantic analysis and eval must
        // have the same view of the program state.
        for i in 0..stmts.len() {
            let stmt = &stmts[i..i + 1];

            // Perform semantic analysis
            match self.semantics.analyze(stmt, &self.eval) {
                Ok(_) => (),
                Err(e) => return EvalResult::Err(e.to_string()),
            };

            // Evaluate AST
            match self.eval.eval(stmt) {
                EvalResult::Ok => (),
                e => return e,
            }
        }

        EvalResult::Ok
    }
}
