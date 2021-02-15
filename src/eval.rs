use std::fmt;

use crate::ast::{BuiltinStatement, Statement};
use crate::parse::parse;
use crate::semantics::analyze;

fn print_help() {
    println!("help\t\tPrint help");
    println!("quit\t\tExit debugger");
}

pub enum EvalResult {
    Ok,
    Quit,
    Err(String),
}

impl fmt::Display for EvalResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalResult::Ok => Ok(()),
            EvalResult::Quit => write!(f, "Quit"),
            EvalResult::Err(msg) => write!(f, "{}", msg),
        }
    }
}

pub struct Eval {}

impl Eval {
    fn eval_builtin(&mut self, builtin: &BuiltinStatement) -> EvalResult {
        match builtin {
            BuiltinStatement::Help => {
                print_help();
                EvalResult::Ok
            }
            BuiltinStatement::Quit => EvalResult::Quit,
            BuiltinStatement::Filesystem(_fs) => unimplemented!(),
            BuiltinStatement::Print(_expr) => unimplemented!(),
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> EvalResult {
        match stmt {
            Statement::AssignStatement(_lhs, _rhs) => unimplemented!(),
            Statement::BlockStatement(_block) => unimplemented!(),
            Statement::JumpStatement(_jump) => unimplemented!(),
            Statement::BuiltinStatement(builtin) => self.eval_builtin(builtin),
            Statement::ExpressionStatement(_expr) => unimplemented!(),
        }
    }

    pub fn new() -> Self {
        Self {}
    }

    pub fn eval(&mut self, cmd: &str) -> EvalResult {
        // Parse input into AST
        let stmts = match parse(cmd) {
            Ok(s) => s,
            Err(e) => return EvalResult::Err(e.to_string()),
        };

        // Perform semantic analysis
        match analyze(&stmts) {
            Ok(_) => (),
            Err(e) => return EvalResult::Err(e.to_string()),
        };

        // Evaluate AST
        for stmt in stmts {
            match self.eval_statement(&stmt) {
                EvalResult::Ok => (),
                res => return res,
            }
        }

        EvalResult::Ok
    }
}
