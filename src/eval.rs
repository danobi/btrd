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

fn eval_statement(stmt: &Statement) -> EvalResult {
    match stmt {
        Statement::BuiltinStatement(BuiltinStatement::Help) => {
            print_help();
            EvalResult::Ok
        }
        Statement::BuiltinStatement(BuiltinStatement::Quit) => EvalResult::Quit,
        _ => EvalResult::Err("Invalid command".to_string()),
    }
}

pub fn eval(cmd: &str) -> EvalResult {
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
        match eval_statement(&stmt) {
            EvalResult::Ok => (),
            res => return res,
        }
    }

    EvalResult::Ok
}
