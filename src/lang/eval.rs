use std::convert::TryInto;
use std::fmt;
use std::io::Write;

use anyhow::{anyhow, bail, Result};

use crate::lang::ast::*;
use crate::lang::parse::parse;
use crate::lang::semantics::SemanticAnalyzer;
use crate::lang::variables::Variables;

#[derive(Clone, PartialEq)]
enum Value {
    /// All integers are internally represented as 128 bit signed to keep things simple
    ///
    /// Any conversion errors (eg. during demotion, to unsigned) will trigger runtime errors
    Integer(i128),
    String(String),
    Boolean(bool),
}

impl Value {
    fn into_integer(self) -> Result<i128> {
        match self {
            Value::Integer(i) => Ok(i),
            _ => bail!("Value is not integer -- semantic analysis bug (tell Daniel)"),
        }
    }

    fn into_boolean(self) -> Result<bool> {
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

/// Internal version of `EvalResult`
///
/// We don't want to expose internal details (like control flow) to anyone outside this module
enum InternalEvalResult {
    Ok,
    Quit,
    Err(String),
    Break,
    Continue,
}

impl InternalEvalResult {
    fn into_eval_result(self) -> EvalResult {
        match self {
            InternalEvalResult::Ok => EvalResult::Ok,
            InternalEvalResult::Quit => EvalResult::Quit,
            InternalEvalResult::Err(s) => EvalResult::Err(s),
            InternalEvalResult::Break => {
                EvalResult::Err("Unhandled control flow eval result (tell Daniel)".to_string())
            }
            InternalEvalResult::Continue => {
                EvalResult::Err("Unhandled control flow eval result (tell Daniel)".to_string())
            }
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
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                let res = lhs_val
                    .checked_add(rhs_val)
                    .ok_or_else(|| anyhow!("{} + {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Minus(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                let res = lhs_val
                    .checked_sub(rhs_val)
                    .ok_or_else(|| anyhow!("{} - {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Multiply(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                let res = lhs_val
                    .checked_mul(rhs_val)
                    .ok_or_else(|| anyhow!("{} * {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Divide(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_div(rhs_val)
                    .ok_or_else(|| anyhow!("{} / {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Modulo(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_rem(rhs_val)
                    .ok_or_else(|| anyhow!("{} % {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::BitOr(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Integer(lhs_val | rhs_val))
            }
            BinaryExpression::BitAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Integer(lhs_val & rhs_val))
            }
            BinaryExpression::BitXor(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Integer(lhs_val ^ rhs_val))
            }
            BinaryExpression::LeftShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                let res = lhs_val
                    .checked_shl(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} << {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::RightShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                let res = lhs_val
                    .checked_shr(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} >> {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::LessThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Boolean(lhs_val < rhs_val))
            }
            BinaryExpression::LessThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Boolean(lhs_val <= rhs_val))
            }
            BinaryExpression::GreaterThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

                Ok(Value::Boolean(lhs_val > rhs_val))
            }
            BinaryExpression::GreaterThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.into_integer()?;

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
                let lhs_val = self.eval_expr(&lhs)?.into_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.into_boolean()?;

                Ok(Value::Boolean(lhs_val || rhs_val))
            }
            BinaryExpression::LogicalAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.into_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.into_boolean()?;

                Ok(Value::Boolean(lhs_val && rhs_val))
            }
        }
    }

    fn eval_unary_expr(&mut self, unary: &UnaryExpression) -> Result<Value> {
        match unary {
            UnaryExpression::BitNot(expr) => {
                let expr_val = self.eval_expr(expr)?.into_integer()?;
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
                let expr_val = self.eval_expr(expr)?.into_integer()?;
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

    fn eval_builtin(&mut self, builtin: &BuiltinStatement) -> InternalEvalResult {
        match builtin {
            BuiltinStatement::Help => self.print_help(),
            BuiltinStatement::Quit => InternalEvalResult::Quit,
            BuiltinStatement::Filesystem(_fs) => unimplemented!(),
            BuiltinStatement::Print(expr) => match self.eval_expr(expr) {
                Ok(v) => match writeln!(self.sink, "{}", v) {
                    Ok(_) => InternalEvalResult::Ok,
                    Err(e) => InternalEvalResult::Err(e.to_string()),
                },
                Err(e) => InternalEvalResult::Err(e.to_string()),
            },
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> InternalEvalResult {
        match stmt {
            Statement::AssignStatement(lhs, rhs) => {
                if let Expression::PrimaryExpression(PrimaryExpression::Identifier(ident)) = lhs {
                    match self.eval_expr(rhs) {
                        Ok(v) => self.variables.insert(ident.clone(), v),
                        Err(e) => return InternalEvalResult::Err(e.to_string()),
                    };

                    InternalEvalResult::Ok
                } else {
                    InternalEvalResult::Err(
                        "Semantic analysis failure: lhs of assignment isn't an ident (tell Daniel)"
                            .to_string(),
                    )
                }
            }
            Statement::BlockStatement(block) => match block {
                BlockStatement::If(cond, true_body, false_body) => {
                    let cond = match self.eval_expr(cond) {
                        Ok(c) => match c.into_boolean() {
                            Ok(v) => v,
                            Err(e) => return InternalEvalResult::Err(e.to_string()),
                        },
                        Err(e) => return InternalEvalResult::Err(e.to_string()),
                    };

                    let stmts = if cond { true_body } else { false_body };
                    for stmt in stmts {
                        match self.eval_statement(stmt) {
                            InternalEvalResult::Ok => (),
                            r @ InternalEvalResult::Err(_)
                            | r @ InternalEvalResult::Quit
                            | r @ InternalEvalResult::Break
                            | r @ InternalEvalResult::Continue => return r,
                        };
                    }

                    InternalEvalResult::Ok
                }
                BlockStatement::While(cond, stmts) => {
                    let mut break_loop = false;
                    loop {
                        let cond = match self.eval_expr(cond) {
                            Ok(c) => match c.into_boolean() {
                                Ok(v) => v,
                                Err(e) => return InternalEvalResult::Err(e.to_string()),
                            },
                            Err(e) => return InternalEvalResult::Err(e.to_string()),
                        };

                        if !cond {
                            break;
                        }

                        for stmt in stmts {
                            match self.eval_statement(stmt) {
                                InternalEvalResult::Ok => (),
                                InternalEvalResult::Break => {
                                    break_loop = true;
                                    break;
                                }
                                InternalEvalResult::Continue => break,
                                r @ InternalEvalResult::Err(_) | r @ InternalEvalResult::Quit => {
                                    return r
                                }
                            };
                        }

                        if break_loop {
                            break;
                        }
                    }

                    InternalEvalResult::Ok
                }
                BlockStatement::For(_ident, _range, _stmts) => {
                    unimplemented!();
                }
            },
            Statement::JumpStatement(jump) => match jump {
                JumpStatement::Break => InternalEvalResult::Break,
                JumpStatement::Continue => InternalEvalResult::Continue,
            },
            Statement::BuiltinStatement(builtin) => self.eval_builtin(builtin),
            Statement::ExpressionStatement(expr) => {
                let val = match self.eval_expr(expr) {
                    Ok(v) => v,
                    Err(e) => return InternalEvalResult::Err(e.to_string()),
                };

                if self.interactive {
                    match writeln!(self.sink, "{}", val) {
                        Ok(_) => (),
                        Err(e) => return InternalEvalResult::Err(e.to_string()),
                    };
                }

                InternalEvalResult::Ok
            }
        }
    }

    fn print_help(&mut self) -> InternalEvalResult {
        let mut s = String::new();

        s += "help\t\tPrint help\n";
        s += "quit\t\tExit debugger\n";

        match write!(self.sink, "{}", s) {
            Ok(_) => InternalEvalResult::Ok,
            Err(e) => InternalEvalResult::Err(e.to_string()),
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
                InternalEvalResult::Ok => (),
                res => return res.into_eval_result(),
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
fn test_if() {
    let tests = vec![
        (r#"x = 3; if x == 3 { print "yep"; }"#, "\"yep\"\n"),
        (
            r#"x = 3; if x != 3 { print "yep"; } else { print "yep"; }"#,
            "\"yep\"\n",
        ),
        (
            r#"x = 3; if x != 3 { print "yep"; } else { print "yep"; if x == 3 { x = 4; } } print x;"#,
            "\"yep\"\n4\n",
        ),
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
fn test_loop() {
    let tests = vec![(
        "x = 0; while x < 5 { if x == 3 { print x; break; } x = x + 1; }",
        "3\n",
    )];

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
