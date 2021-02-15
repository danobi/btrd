use std::convert::TryInto;
use std::fmt;
use std::io::Write;

use anyhow::{anyhow, bail, Result};

use crate::ast::*;
use crate::parse::parse;
use crate::semantics::SemanticAnalyzer;
use crate::variables::Variables;

#[derive(Clone, PartialEq)]
enum Value {
    /// All integers are internally represented as 64 bit signed to keep things simple
    ///
    /// Any conversion errors (eg. during demotion, to unsigned) will trigger runtime errors
    Integer(i64),
    String(String),
    Boolean(bool),
}

impl Value {
    fn to_integer(self) -> Result<i64> {
        match self {
            Value::Integer(i) => Ok(i),
            _ => bail!("Value is not integer -- semantic analysis bug (tell Daniel)"),
        }
    }

    fn to_boolean(self) -> Result<bool> {
        match self {
            Value::Boolean(b) => Ok(b),
            _ => bail!("Value is not boolean -- semantic analysis bug (tell Daniel)"),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Integer(i) => write!(f, "{}", i),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Boolean(b) => {
                write!(f, "{}", if *b { "true" } else { "false" })
            }
        }
    }
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

pub struct Eval<'a> {
    sink: &'a mut dyn Write,
    interactive: bool,
    semantics: SemanticAnalyzer,
    variables: Variables<Value>,
}

impl<'a> Eval<'a> {
    fn eval_primary_expr(&mut self, expr: &PrimaryExpression) -> Result<Value> {
        let val = match expr {
            PrimaryExpression::Identifier(ident) => self
                .variables
                .get(ident)
                .ok_or_else(|| anyhow!("Unknown variable: {}", ident))?
                .clone(),
            PrimaryExpression::Constant(c) => match c {
                Constant::Integer(i) => Value::Integer(*i),
                Constant::Boolean(b) => Value::Boolean(*b),
            },
            PrimaryExpression::Str(s) => Value::String(s.clone()),
            PrimaryExpression::Paren(expr) => self.eval_expr(expr)?,
        };

        Ok(val)
    }

    fn eval_binop_expr(&mut self, binop: &BinaryExpression) -> Result<Value> {
        match binop {
            BinaryExpression::Plus(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                let res = lhs_val
                    .checked_add(rhs_val)
                    .ok_or_else(|| anyhow!("{} + {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Minus(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                let res = lhs_val
                    .checked_sub(rhs_val)
                    .ok_or_else(|| anyhow!("{} - {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Multiply(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                let res = lhs_val
                    .checked_mul(rhs_val)
                    .ok_or_else(|| anyhow!("{} * {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Divide(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_div(rhs_val)
                    .ok_or_else(|| anyhow!("{} / {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Modulo(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_rem(rhs_val)
                    .ok_or_else(|| anyhow!("{} % {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::BitOr(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Integer(lhs_val | rhs_val))
            }
            BinaryExpression::BitAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Integer(lhs_val & rhs_val))
            }
            BinaryExpression::BitXor(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Integer(lhs_val ^ rhs_val))
            }
            BinaryExpression::LeftShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                let res = lhs_val
                    .checked_shl(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} << {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::RightShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                let res = lhs_val
                    .checked_shr(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} >> {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::LessThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Boolean(lhs_val < rhs_val))
            }
            BinaryExpression::LessThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Boolean(lhs_val <= rhs_val))
            }
            BinaryExpression::GreaterThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Boolean(lhs_val > rhs_val))
            }
            BinaryExpression::GreaterThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.to_integer()?;

                Ok(Value::Boolean(lhs_val >= rhs_val))
            }
            BinaryExpression::Equals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?;
                let rhs_val = self.eval_expr(&rhs)?;

                Ok(Value::Boolean(lhs_val == rhs_val))
            }
            BinaryExpression::NotEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?;
                let rhs_val = self.eval_expr(&rhs)?;

                Ok(Value::Boolean(lhs_val != rhs_val))
            }
            BinaryExpression::LogicalOr(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.to_boolean()?;

                Ok(Value::Boolean(lhs_val || rhs_val))
            }
            BinaryExpression::LogicalAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.to_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.to_boolean()?;

                Ok(Value::Boolean(lhs_val && rhs_val))
            }
        }
    }

    fn eval_unary_expr(&mut self, unary: &UnaryExpression) -> Result<Value> {
        match unary {
            UnaryExpression::BitNot(expr) => {
                let expr_val = self.eval_expr(expr)?.to_integer()?;
                Ok(Value::Integer(!expr_val))
            }
            UnaryExpression::Not(expr) => {
                let expr_val = self.eval_expr(expr)?;
                match expr_val {
                    Value::Integer(i) => Ok(Value::Boolean(i == 0)),
                    Value::Boolean(b) => Ok(Value::Boolean(!b)),
                    _ => bail!("Semantic analysis failure: UnaryNot on non-integer and non-boolean (tell Daniel)"),
                }
            }
            UnaryExpression::Minus(expr) => {
                let expr_val = self.eval_expr(expr)?.to_integer()?;
                Ok(Value::Integer(-expr_val))
            }
        }
    }

    fn eval_expr(&mut self, expr: &Expression) -> Result<Value> {
        match expr {
            Expression::PrimaryExpression(p) => self.eval_primary_expr(p),
            Expression::FieldAccess(_expr, _field) => {
                // TODO: implement after builtin functions are added
                unimplemented!()
            }
            Expression::ArrayIndex(_expr, _index) => {
                // TODO: implement after builtin functions are added
                unimplemented!()
            }
            Expression::FunctionCall(_expr, _args) => {
                // TODO: implement when builtin functions are added
                unimplemented!()
            }
            Expression::BinaryExpression(b) => self.eval_binop_expr(b),
            Expression::UnaryExpression(u) => self.eval_unary_expr(u),
        }
    }

    fn eval_builtin(&mut self, builtin: &BuiltinStatement) -> EvalResult {
        match builtin {
            BuiltinStatement::Help => self.print_help(),
            BuiltinStatement::Quit => EvalResult::Quit,
            BuiltinStatement::Filesystem(_fs) => unimplemented!(),
            BuiltinStatement::Print(expr) => match self.eval_expr(expr) {
                Ok(v) => match writeln!(self.sink, "{}", v) {
                    Ok(_) => EvalResult::Ok,
                    Err(e) => EvalResult::Err(e.to_string()),
                },
                Err(e) => return EvalResult::Err(e.to_string()),
            },
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> EvalResult {
        match stmt {
            Statement::AssignStatement(lhs, rhs) => {
                if let Expression::PrimaryExpression(PrimaryExpression::Identifier(ident)) = lhs {
                    match self.eval_expr(rhs) {
                        Ok(v) => self.variables.insert(ident.clone(), v),
                        Err(e) => return EvalResult::Err(e.to_string()),
                    };

                    EvalResult::Ok
                } else {
                    EvalResult::Err(
                        "Semantic analysis failure: lhs of assignment isn't an ident (tell Daniel)"
                            .to_string(),
                    )
                }
            }
            Statement::BlockStatement(block) => match block {
                BlockStatement::If(cond, true_body, false_body) => {
                    let cond = match self.eval_expr(cond) {
                        Ok(c) => match c.to_boolean() {
                            Ok(v) => v,
                            Err(e) => return EvalResult::Err(e.to_string()),
                        },
                        Err(e) => return EvalResult::Err(e.to_string()),
                    };

                    let stmts = if cond { true_body } else { false_body };
                    for stmt in stmts {
                        match self.eval_statement(stmt) {
                            EvalResult::Ok => (),
                            r @ EvalResult::Err(_) | r @ EvalResult::Quit => return r,
                        };
                    }

                    EvalResult::Ok
                }
                BlockStatement::While(cond, stmts) => {
                    loop {
                        let cond = match self.eval_expr(cond) {
                            Ok(c) => match c.to_boolean() {
                                Ok(v) => v,
                                Err(e) => return EvalResult::Err(e.to_string()),
                            },
                            Err(e) => return EvalResult::Err(e.to_string()),
                        };

                        if !cond {
                            break;
                        }

                        for stmt in stmts {
                            match stmt {
                                Statement::JumpStatement(JumpStatement::Break) => break,
                                Statement::JumpStatement(JumpStatement::Continue) => continue,
                                _ => (),
                            };

                            match self.eval_statement(stmt) {
                                EvalResult::Ok => (),
                                r @ EvalResult::Err(_) | r @ EvalResult::Quit => return r,
                            };
                        }
                    }

                    EvalResult::Ok
                }
                BlockStatement::For(_ident, _range, _stmts) => {
                    unimplemented!();
                }
            },
            Statement::JumpStatement(_) => {
                panic!("Jump statement not handled in loop implementation")
            }
            Statement::BuiltinStatement(builtin) => self.eval_builtin(builtin),
            Statement::ExpressionStatement(expr) => {
                let val = match self.eval_expr(expr) {
                    Ok(v) => v,
                    Err(e) => return EvalResult::Err(e.to_string()),
                };

                if self.interactive {
                    match writeln!(self.sink, "{}", val) {
                        Ok(_) => (),
                        Err(e) => return EvalResult::Err(e.to_string()),
                    };
                }

                EvalResult::Ok
            }
        }
    }

    fn print_help(&mut self) -> EvalResult {
        let mut s = String::new();

        s += "help\t\tPrint help\n";
        s += "quit\t\tExit debugger\n";

        match write!(self.sink, "{}", s) {
            Ok(_) => EvalResult::Ok,
            Err(e) => EvalResult::Err(e.to_string()),
        }
    }

    /// Create a new `Eval` instance
    ///
    /// `sink` is where output should be written. eg. result of `print` statements
    ///
    /// `interactive` sets whether or not expression statements should print the result (useful
    /// when human is at a REPL)
    pub fn new(sink: &'a mut dyn Write, interactive: bool) -> Self {
        Self {
            sink,
            interactive,
            semantics: SemanticAnalyzer::new(),
            variables: Variables::new(),
        }
    }

    pub fn eval(&mut self, cmd: &str) -> EvalResult {
        // Parse input into AST
        let stmts = match parse(cmd) {
            Ok(s) => s,
            Err(e) => return EvalResult::Err(e.to_string()),
        };

        // Perform semantic analysis
        match self.semantics.analyze(&stmts) {
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

#[test]
fn test_expression() {
    let tests = vec![
        ("print ~8;", "-9\n"),
        ("print -8;", "-8\n"),
        ("print !8;", "false\n"),
        ("print !0;", "true\n"),
        ("print !!8;", "true\n"),
        ("print 5 + 5;", "10\n"),
        ("print 100 -3;", "97\n"),
        ("print 100* 3;", "300\n"),
        ("print 99 / 3;", "33\n"),
        ("print 100 / 3;", "33\n"),
        ("print 100 % 3;", "1\n"),
        ("print 1 == 1;", "true\n"),
        ("print true == false;", "false\n"),
        ("print true != false;", "true\n"),
        ("print true != false && 2 == 2;", "true\n"),
        ("print true != false && 2 != 2;", "false\n"),
        ("print true != false || 2 != 2;", "true\n"),
        ("print 7 & 1;", "1\n"),
        ("print 0 | 1 | 2;", "3\n"),
        ("print 1 ^ 2;", "3\n"),
        ("print 1 << 2;", "4\n"),
        ("print 1 << 3;", "8\n"),
        ("print 1 < 3;", "true\n"),
        ("print 3 <= 3;", "true\n"),
        ("print 3 > 3;", "false\n"),
        ("print 3 >= 3;", "true\n"),
    ];

    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);
        match eval.eval(input) {
            EvalResult::Ok => (),
            _ => assert!(false),
        };
        assert_eq!(
            String::from_utf8(output).expect("Output not utf-8"),
            expected
        );
    }
}

#[test]
fn test_interactive() {
    let mut output = Vec::new();
    let mut eval = Eval::new(&mut output, true);
    match eval.eval("2+3;") {
        EvalResult::Ok => (),
        _ => assert!(false),
    };
    assert_eq!(String::from_utf8(output).expect("Output not utf-8"), "5\n");
}
