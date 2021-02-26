use std::collections::VecDeque;
use std::convert::TryInto;
use std::io::Write;

use anyhow::{anyhow, bail, ensure, Result};
use nix::unistd::getcwd;

use super::value::{Array, Struct, Value};
use crate::btrfs::definitions::{BTRFS_KEY, BTRFS_SEARCH_KEY, STRUCTS};
use crate::btrfs::fs::Fs;
use crate::lang::ast::*;
use crate::lang::functions::Function;
use crate::lang::variables::Variables;

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
    variables: Variables<Value>,
    fs: Option<Fs>,
}

impl<'a> Eval<'a> {
    fn eval_primary_expr(&self, expr: &PrimaryExpression) -> Result<Value> {
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

    fn eval_binop_expr(&self, binop: &BinaryExpression) -> Result<Value> {
        match binop {
            BinaryExpression::Plus(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?;
                let rhs_val = self.eval_expr(&rhs)?;

                match (lhs_val, rhs_val) {
                    (Value::Integer(l), Value::Integer(r)) => {
                        let res = l
                            .checked_add(r)
                            .ok_or_else(|| anyhow!("{} + {} overflows", l, r))?;

                        Ok(Value::Integer(res))
                    }
                    (Value::Array(mut arr), v) => {
                        arr.vec.push(v);

                        Ok(Value::Array(arr))
                    }
                    (l, r) => bail!(
                        "Cannot add types '{}' and '{}'",
                        l.short_display(),
                        r.short_display()
                    ),
                }
            }
            BinaryExpression::Minus(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                let res = lhs_val
                    .checked_sub(rhs_val)
                    .ok_or_else(|| anyhow!("{} - {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Multiply(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                let res = lhs_val
                    .checked_mul(rhs_val)
                    .ok_or_else(|| anyhow!("{} * {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Divide(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_div(rhs_val)
                    .ok_or_else(|| anyhow!("{} / {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::Modulo(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                if rhs_val == 0 {
                    bail!("Divide by zero");
                }

                let res = lhs_val
                    .checked_rem(rhs_val)
                    .ok_or_else(|| anyhow!("{} % {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::BitOr(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Integer(lhs_val | rhs_val))
            }
            BinaryExpression::BitAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Integer(lhs_val & rhs_val))
            }
            BinaryExpression::BitXor(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Integer(lhs_val ^ rhs_val))
            }
            BinaryExpression::LeftShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                let res = lhs_val
                    .checked_shl(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} << {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::RightShift(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                let res = lhs_val
                    .checked_shr(rhs_val.try_into()?)
                    .ok_or_else(|| anyhow!("{} >> {} overflows", lhs_val, rhs_val))?;

                Ok(Value::Integer(res))
            }
            BinaryExpression::LessThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Boolean(lhs_val < rhs_val))
            }
            BinaryExpression::LessThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Boolean(lhs_val <= rhs_val))
            }
            BinaryExpression::GreaterThan(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

                Ok(Value::Boolean(lhs_val > rhs_val))
            }
            BinaryExpression::GreaterThanEquals(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_integer()?;
                let rhs_val = self.eval_expr(&rhs)?.as_integer()?;

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
                let lhs_val = self.eval_expr(&lhs)?.as_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.as_boolean()?;

                Ok(Value::Boolean(lhs_val || rhs_val))
            }
            BinaryExpression::LogicalAnd(lhs, rhs) => {
                let lhs_val = self.eval_expr(&lhs)?.as_boolean()?;
                let rhs_val = self.eval_expr(&rhs)?.as_boolean()?;

                Ok(Value::Boolean(lhs_val && rhs_val))
            }
        }
    }

    fn eval_unary_expr(&self, unary: &UnaryExpression) -> Result<Value> {
        match unary {
            UnaryExpression::BitNot(expr) => {
                let expr_val = self.eval_expr(expr)?.as_integer()?;
                Ok(Value::Integer(!expr_val))
            }
            UnaryExpression::Not(expr) => {
                let expr_val = self.eval_expr(expr)?;
                match expr_val {
                    Value::Integer(i) => Ok(Value::Boolean(i == 0)),
                    Value::Boolean(b) => Ok(Value::Boolean(!b)),
                    v => bail!("Expected integer or boolean, got '{}'", v.short_display()),
                }
            }
            UnaryExpression::Minus(expr) => {
                let expr_val = self.eval_expr(expr)?.as_integer()?;
                Ok(Value::Integer(-expr_val))
            }
        }
    }

    fn eval_function(&self, func: &Expression, args: &[Expression]) -> Result<Value> {
        match self.eval_expr(func)?.as_function()? {
            f @ Function::Key => {
                ensure!(args.len() == 4, "'{}()' requires 4 arguments", f);

                // Evaluate args
                let mut arg_vals = VecDeque::with_capacity(args.len());
                for arg in args {
                    let val = self.eval_expr(arg)?;
                    // Will bail if non-integer
                    let _ = val.as_integer()?;
                    arg_vals.push_back(val);
                }

                let zeros = vec![0; BTRFS_SEARCH_KEY.size()];
                let mut key = Struct::from_bytes(&*BTRFS_SEARCH_KEY, None, &zeros)?;

                *(key.field_mut("min_objectid")?) = arg_vals.pop_front().unwrap();
                *(key.field_mut("max_objectid")?) = Value::Integer(u64::MAX.into());

                *(key.field_mut("min_type")?) = arg_vals.pop_front().unwrap();
                *(key.field_mut("max_type")?) = Value::Integer(u8::MAX.into());

                *(key.field_mut("min_offset")?) = arg_vals.pop_front().unwrap();
                *(key.field_mut("max_offset")?) = Value::Integer(u64::MAX.into());

                *(key.field_mut("min_transid")?) = arg_vals.pop_front().unwrap();
                *(key.field_mut("max_transid")?) = Value::Integer(u64::MAX.into());

                Ok(Value::Struct(key))
            }
            f @ Function::Search => {
                ensure!(args.len() == 2, "'{}()' requires 2 arguments", f);

                let tree_id = self.eval_expr(&args[0])?.as_integer()?;
                let key_val = self.eval_expr(&args[1])?;
                let key = key_val.as_struct()?;
                ensure!(
                    key.name == BTRFS_SEARCH_KEY.name,
                    "Argument 2 of search() must be 'struct {}",
                    BTRFS_SEARCH_KEY.name
                );

                let chunks = match &self.fs {
                    Some(fs) => fs.search(
                        tree_id.try_into()?,
                        key.field("min_objectid")?.as_integer()?.try_into()?,
                        key.field("max_objectid")?.as_integer()?.try_into()?,
                        key.field("min_type")?.as_integer()?.try_into()?,
                        key.field("max_type")?.as_integer()?.try_into()?,
                        key.field("min_offset")?.as_integer()?.try_into()?,
                        key.field("max_offset")?.as_integer()?.try_into()?,
                        key.field("min_transid")?.as_integer()?.try_into()?,
                        key.field("max_transid")?.as_integer()?.try_into()?,
                    )?,
                    None => bail!(
                        "No filesystem set, set a filesystem first with 'filesystem \"/path\"'"
                    ),
                };

                let mut arr = Vec::new();
                for (header, bytes) in chunks {
                    let s = STRUCTS.iter().find_map(|s| {
                        if (s.key_match)(
                            header.objectid.into(),
                            header.ty.into(),
                            header.offset.into(),
                        ) {
                            return Some(s);
                        }

                        None
                    });

                    match s {
                        Some(s) => arr.push(
                            Value::Struct(
                                Struct::from_bytes(
                                    s,
                                    Some((
                                        header.objectid.into(),
                                        header.ty.into(),
                                        header.offset.into()
                                    )),
                                    &bytes)?)
                        ),
                        None => eprintln!(
                            "Warning: failed to find a matching on-disk struct for key [{}, {}, {}]",
                            header.objectid, header.ty, header.offset
                        ),
                    }
                }

                Ok(Value::Array(Array {
                    vec: arr,
                    is_hist: false,
                }))
            }
            f @ Function::TypeOf => {
                ensure!(args.len() == 1, "'{}()' requires 1 argument", f);

                let expr = self.eval_expr(&args[0])?;
                let ty_str = match expr {
                    Value::Integer(_) => "integer".to_string(),
                    Value::String(_) => "string".to_string(),
                    Value::Boolean(_) => "boolean".to_string(),
                    Value::Array(_) => "array".to_string(),
                    Value::Function(_) => "function".to_string(),
                    Value::Struct(s) => format!("struct {}", s.name),
                };

                Ok(Value::String(ty_str))
            }
            f @ Function::KeyOf => {
                ensure!(args.len() == 1, "'{}()' requires 1 argument", f);

                let expr = self.eval_expr(&args[0])?;
                let s = expr.as_struct()?;

                if let Some((oid, ty, off)) = s.key {
                    let zeros = vec![0; BTRFS_KEY.size()];
                    let mut key = Struct::from_bytes(&*BTRFS_KEY, None, &zeros)?;

                    *(key.field_mut("objectid")?) = Value::Integer(oid);
                    *(key.field_mut("type")?) = Value::Integer(ty);
                    *(key.field_mut("offset")?) = Value::Integer(off);

                    Ok(Value::Struct(key))
                } else {
                    bail!("Could not take '{}()' struct with no on-disk key", f);
                }
            }
            f @ Function::Len => {
                ensure!(args.len() == 1, "'{}()' requires 1 argument", f);
                let expr = self.eval_expr(&args[0])?;

                Ok(Value::Integer(expr.as_vec()?.len().try_into()?))
            }
            f @ Function::Hist => {
                ensure!(args.is_empty(), "'{}()' takes no arguments", f);

                Ok(Value::Array(Array {
                    vec: Vec::new(),
                    is_hist: true,
                }))
            }
        }
    }

    fn eval_expr(&self, expr: &Expression) -> Result<Value> {
        match expr {
            Expression::PrimaryExpression(p) => self.eval_primary_expr(p),
            Expression::FieldAccess(expr, field) => {
                let expr = self.eval_expr(expr)?;
                let s = expr.as_struct()?;

                let ident = match &**field {
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(i))) => {
                        i
                    }
                    _ => bail!("Field in a field access must be an identifier"),
                };

                Ok(s.field(ident)?.clone())
            }
            Expression::ArrayIndex(expr, index) => {
                let arr = self.eval_expr(expr)?;
                let vec = arr.as_vec()?;
                let idx = self.eval_expr(index)?.as_integer()?;

                if let Some(v) = vec.get::<usize>(idx.try_into()?) {
                    Ok(v.clone())
                } else {
                    bail!("Index {} out of range, length is {}", idx, vec.len());
                }
            }
            Expression::FunctionCall(func, args) => self.eval_function(func, args),
            Expression::BinaryExpression(b) => self.eval_binop_expr(b),
            Expression::UnaryExpression(u) => self.eval_unary_expr(u),
        }
    }

    fn eval_builtin(&mut self, builtin: &BuiltinStatement) -> InternalEvalResult {
        match builtin {
            BuiltinStatement::Help => self.print_help(),
            BuiltinStatement::Quit => InternalEvalResult::Quit,
            BuiltinStatement::Filesystem(fs) => {
                self.fs = match self.eval_expr(fs) {
                    Ok(val) => match val.as_string() {
                        Ok(path) => match Fs::new(path) {
                            Ok(fs) => Some(fs),
                            Err(e) => return InternalEvalResult::Err(e.to_string()),
                        },
                        Err(e) => return InternalEvalResult::Err(e.to_string()),
                    },
                    Err(e) => return InternalEvalResult::Err(e.to_string()),
                };

                InternalEvalResult::Ok
            }
            BuiltinStatement::Print(expr) => match self.eval_expr(expr) {
                Ok(v) => {
                    let out = match v {
                        Value::Array(arr) if arr.is_hist => match arr.as_hist() {
                            Ok(o) => o,
                            Err(e) => return InternalEvalResult::Err(e.to_string()),
                        },
                        _ => format!("{}", v),
                    };

                    match writeln!(self.sink, "{}", out) {
                        Ok(_) => InternalEvalResult::Ok,
                        Err(e) => InternalEvalResult::Err(e.to_string()),
                    }
                }
                Err(e) => InternalEvalResult::Err(e.to_string()),
            },
        }
    }

    fn eval_if(
        &mut self,
        cond: &Expression,
        true_body: &[Statement],
        false_body: &[Statement],
    ) -> InternalEvalResult {
        let cond = match self.eval_expr(cond) {
            Ok(c) => match c.as_boolean() {
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

    fn eval_while(&mut self, cond: &Expression, stmts: &[Statement]) -> InternalEvalResult {
        'outer: loop {
            let cond = match self.eval_expr(cond) {
                Ok(c) => match c.as_boolean() {
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
                        break 'outer;
                    }
                    InternalEvalResult::Continue => break,
                    r @ InternalEvalResult::Err(_) | r @ InternalEvalResult::Quit => return r,
                };
            }
        }

        InternalEvalResult::Ok
    }

    fn eval_for(
        &mut self,
        ident: &Expression,
        range: &Expression,
        stmts: &[Statement],
    ) -> InternalEvalResult {
        let ident = match ident {
            Expression::PrimaryExpression(PrimaryExpression::Identifier(i)) => i,
            _ => {
                return InternalEvalResult::Err(
                    "Variable in for loop must be an identifier".to_string(),
                )
            }
        };

        let range = match self.eval_expr(range) {
            Ok(r) => r,
            Err(e) => return InternalEvalResult::Err(e.to_string()),
        };

        let range_vec = match range.as_vec() {
            Ok(r) => r,
            Err(e) => return InternalEvalResult::Err(e.to_string()),
        };

        'outer: for item in range_vec {
            self.variables.insert(ident.clone(), item.clone());

            for stmt in stmts {
                match self.eval_statement(stmt) {
                    InternalEvalResult::Ok => (),
                    InternalEvalResult::Break => {
                        break 'outer;
                    }
                    InternalEvalResult::Continue => break,
                    r @ InternalEvalResult::Err(_) | r @ InternalEvalResult::Quit => return r,
                };
            }
        }

        InternalEvalResult::Ok
    }

    /// Evaluates where the left hand side of an assignment should write to
    fn eval_lhs_assign(&mut self, expr: &Expression) -> Result<&mut Value> {
        match expr {
            Expression::PrimaryExpression(pe) => match pe {
                PrimaryExpression::Identifier(ident) => Ok(self
                    .variables
                    .get_mut(ident)
                    .ok_or_else(|| anyhow!("Unknown variable: {}", ident))?),
                _ => bail!("Expected identifier in LHS of assignment"),
            },
            Expression::FieldAccess(expr, field) => {
                let ident = match &**field {
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(i))) => {
                        i
                    }
                    _ => bail!("Field in a field access must be an identifier"),
                };

                match self.eval_lhs_assign(expr)? {
                    Value::Struct(s) => Ok(s.field_mut(ident)?),
                    _ => bail!("Field access must be used on a struct"),
                }
            }
            Expression::ArrayIndex(expr, index) => {
                let idx = self.eval_expr(index)?.as_integer()?;
                let lhs = self.eval_lhs_assign(expr)?;

                match lhs {
                    Value::Array(arr) => {
                        let len = arr.vec.len();
                        Ok(arr.vec.get_mut::<usize>(idx.try_into()?).ok_or_else(|| {
                            anyhow!("Index {} out of range, length is {}", idx, len)
                        })?)
                    }
                    _ => bail!("Array index must be used on an array"),
                }
            }
            Expression::FunctionCall(_, _) => {
                bail!("Unexpected function call in LHS of assignment")
            }
            Expression::BinaryExpression(_) => {
                bail!("Unexpected binary expression in LHS of assignment")
            }
            Expression::UnaryExpression(_) => {
                bail!("Unexpected unary expression in LHS of assignment")
            }
        }
    }

    fn eval_statement(&mut self, stmt: &Statement) -> InternalEvalResult {
        match stmt {
            Statement::AssignStatement(lhs, rhs) => {
                let rhs_val = match self.eval_expr(rhs) {
                    Ok(v) => v,
                    Err(e) => return InternalEvalResult::Err(e.to_string()),
                };

                // Handle whole variable assignment (eg `x = 3`)
                if let Expression::PrimaryExpression(PrimaryExpression::Identifier(ident)) = lhs {
                    self.variables.insert(ident.clone(), rhs_val);
                    return InternalEvalResult::Ok;
                }

                // Handle partial variable assignment (eg `x.foo = 3`)
                match self.eval_lhs_assign(lhs) {
                    Ok(r) => *r = rhs_val,
                    Err(e) => return InternalEvalResult::Err(e.to_string()),
                };

                InternalEvalResult::Ok
            }
            Statement::BlockStatement(block) => match block {
                BlockStatement::If(cond, true_body, false_body) => {
                    self.variables.push_scope();
                    let ret = self.eval_if(cond, true_body, false_body);
                    self.variables.pop_scope();

                    ret
                }
                BlockStatement::While(cond, stmts) => {
                    self.variables.push_scope();
                    let ret = self.eval_while(cond, stmts);
                    self.variables.pop_scope();

                    ret
                }
                BlockStatement::For(ident, range, stmts) => {
                    self.variables.push_scope();
                    let ret = self.eval_for(ident, range, stmts);
                    self.variables.pop_scope();

                    ret
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
        let help = vec![
            ("Commands", ""),
            ("--------------------", ""),
            ("help", "Print help"),
            ("quit", "Exit debugger"),
            (
                "filesystem <string>",
                "Debug <string> (<string> must be a path to a mounted btrfs filesystem)",
            ),
            (
                "print <expression>",
                "Evaluate <expression> and print result",
            ),
            ("", ""),
            ("Functions", ""),
            ("--------------------", ""),
            (
                "key(objectid, type, offset, transid)",
                "Returns a key to be used in `search()`",
            ),
            (
                "search(treeid, key)",
                "Returns an array of search results based on `treeid` and `key`",
            ),
            (
                "keyof(expr)",
                "Returns the corresponding disk key (if any) of the expression",
            ),
            ("typeof(expr)", "Returns the type of `expr` as a string"),
            ("len(expr)", "Returns the length of an array"),
            ("hist()", "Returns a histogram (an array that `print()` will format)"),
        ];

        let width = help
            .iter()
            .max_by_key(|p| p.0.len())
            .map_or(0, |p| p.0.len() + 4);
        let mut s = String::new();
        for (l, r) in help {
            s += &format!("{:width$}{}\n", l, r, width = width);
        }

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
        let fs = match getcwd() {
            Ok(cwd) => Fs::new(cwd).ok(),
            Err(_) => None,
        };

        Self {
            sink,
            interactive,
            variables: Variables::new(Value::Integer, Value::Function),
            fs,
        }
    }

    pub fn eval(&mut self, stmts: &[Statement]) -> EvalResult {
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
    {
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
            ("print !1;", "false\n"),
            ("print !!1;", "true\n"),
            ("print !!!!!5;", "false\n"),
            ("print ~1;", "-2\n"),
            ("print -~~~5;", "6\n"),
            ("print --5;", "5\n"),
        ];

        use crate::lang::parse::parse;
        for (input, expected) in tests {
            let mut output = Vec::new();
            let mut eval = Eval::new(&mut output, false);
            match eval.eval(&parse(input).expect("Failed to parse")) {
                EvalResult::Ok => (),
                _ => assert!(false),
            };
            assert_eq!(
                String::from_utf8(output).expect("Output not utf-8"),
                expected
            );
        }
    }
    {
        let tests = vec![
            (r#"!"str";"#),
            (r#"~"asdf";"#),
            ("~true;"),
            (r#"-"str";"#),
            ("-true;"),
            ("true + 3;"),
            (r#""string" * false;"#),
            (r#""string" / 1234;"#),
            (r#""string" % 1234;"#),
            ("false && 3;"),
            ("false || 3;"),
            ("false | 3;"),
            ("3 & true;"),
            ("3 ^ true;"),
            (r#"1 << "asdf";"#),
            ("true >> 3;"),
            (r#"1 < "str";"#),
            (r#"1 > "str";"#),
            (r#"1 >= "str";"#),
            (r#"1 <= "str";"#),
        ];

        use crate::lang::parse::parse;
        for input in tests {
            let mut output = Vec::new();
            let mut eval = Eval::new(&mut output, false);
            match eval.eval(&parse(input).expect("Failed to parse")) {
                EvalResult::Err(_) => (),
                _ => assert!(false, "Eval succeeded when should have failed"),
            };
        }
    }
}

#[test]
fn test_if() {
    let tests = vec![
        (r#"x = 3; if x == 3 { print "yep"; }"#, "\"yep\"\n"),
        (
            r#"x = 3; if x != 3 { print "nope"; } else { print "yep"; }"#,
            "\"yep\"\n",
        ),
        (
            r#"x = 3; if x != 3 { print "nope"; } else { print "yep"; if x == 3 { x = 4; } } print x;"#,
            "\"yep\"\n4\n",
        ),
    ];

    use crate::lang::parse::parse;
    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);
        match eval.eval(&parse(input).expect("Failed to parse")) {
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

    use crate::lang::parse::parse;
    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);
        match eval.eval(&parse(input).expect("Failed to parse")) {
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
    use crate::lang::parse::parse;
    let mut output = Vec::new();
    let mut eval = Eval::new(&mut output, true);
    match eval.eval(&parse("2+3;").expect("Failed to parse")) {
        EvalResult::Ok => (),
        _ => assert!(false),
    };
    assert_eq!(String::from_utf8(output).expect("Output not utf-8"), "5\n");
}

#[cfg(test)]
unsafe fn any_as_u8_slice<T: Sized>(p: &T) -> &[u8] {
    ::std::slice::from_raw_parts((p as *const T) as *const u8, ::std::mem::size_of::<T>())
}

#[cfg(test)]
use crate::btrfs::structs::{Field as BtrfsField, Struct as BtrfsStruct, Type as BtrfsType};

#[cfg(target_endian = "little")]
#[test]
fn test_struct_deserialize() {
    {
        let struct_def = BtrfsStruct {
            name: "some_struct",
            key_match: |_, _, _| false,
            fields: vec![
                BtrfsField {
                    name: Some("one"),
                    ty: BtrfsType::U64,
                },
                BtrfsField {
                    name: Some("two"),
                    ty: BtrfsType::U32,
                },
                BtrfsField {
                    name: Some("three"),
                    ty: BtrfsType::U16,
                },
                BtrfsField {
                    name: Some("four"),
                    ty: BtrfsType::U8,
                },
            ],
        };

        #[repr(C, packed)]
        struct SomeStruct {
            one: u64,
            two: u32,
            three: u16,
            four: u8,
        }

        let s = SomeStruct {
            one: 11111,
            two: 2222,
            three: 333,
            four: 4,
        };

        let interpreted = Struct::from_bytes(&struct_def, None, unsafe { any_as_u8_slice(&s) })
            .expect("Failed to interpret struct");

        assert_eq!(interpreted.name, "some_struct");
        assert_eq!(interpreted.fields.len(), 4);
        assert_eq!(interpreted.fields[0].name, "one");
        assert_eq!(
            interpreted.fields[0].value.as_integer().expect("not int"),
            11111
        );
        assert_eq!(interpreted.fields[1].name, "two");
        assert_eq!(
            interpreted.fields[1].value.as_integer().expect("not int"),
            2222
        );
        assert_eq!(interpreted.fields[2].name, "three");
        assert_eq!(
            interpreted.fields[2].value.as_integer().expect("not int"),
            333
        );
        assert_eq!(interpreted.fields[3].name, "four");
        assert_eq!(
            interpreted.fields[3].value.as_integer().expect("not int"),
            4
        );
    }
    {
        let struct_def = BtrfsStruct {
            name: "some_struct",
            key_match: |_, _, _| false,
            fields: vec![
                BtrfsField {
                    name: Some("one"),
                    ty: BtrfsType::Array(Box::new(BtrfsType::U32), 5),
                },
                BtrfsField {
                    name: Some("two"),
                    ty: BtrfsType::U64,
                },
            ],
        };

        #[repr(C, packed)]
        struct SomeStruct {
            one: [u32; 5],
            two: u64,
        }

        let s = SomeStruct {
            one: [666, 555, 444, 333, 222],
            two: 11111,
        };

        let interpreted = Struct::from_bytes(&struct_def, None, unsafe { any_as_u8_slice(&s) })
            .expect("Failed to interpret struct");

        assert_eq!(interpreted.name, "some_struct");
        assert_eq!(interpreted.fields.len(), 2);

        assert_eq!(interpreted.fields[0].name, "one");
        let vec = interpreted.fields[0].value.as_vec().expect("not vec");
        assert_eq!(vec[0].as_integer().expect("not int"), 666);
        assert_eq!(vec[1].as_integer().expect("not int"), 555);
        assert_eq!(vec[2].as_integer().expect("not int"), 444);
        assert_eq!(vec[3].as_integer().expect("not int"), 333);
        assert_eq!(vec[4].as_integer().expect("not int"), 222);

        assert_eq!(interpreted.fields[1].name, "two");
        assert_eq!(
            interpreted.fields[1].value.as_integer().expect("not int"),
            11111
        );
    }
    {
        let struct_def = BtrfsStruct {
            name: "some_struct",
            key_match: |_, _, _| false,
            fields: vec![BtrfsField {
                name: None,
                ty: BtrfsType::Struct(BtrfsStruct {
                    name: "_anon_struct",
                    key_match: |_, _, _| false,
                    fields: vec![
                        BtrfsField {
                            name: Some("one"),
                            ty: BtrfsType::U64,
                        },
                        BtrfsField {
                            name: Some("two"),
                            ty: BtrfsType::U64,
                        },
                        BtrfsField {
                            name: Some("inner"),
                            ty: BtrfsType::Struct(BtrfsStruct {
                                name: "inner_struct",
                                key_match: |_, _, _| false,
                                fields: vec![BtrfsField {
                                    name: Some("three"),
                                    ty: BtrfsType::U8,
                                }],
                            }),
                        },
                    ],
                }),
            }],
        };

        #[repr(C, packed)]
        struct InnerStruct {
            three: u8,
        }

        #[repr(C, packed)]
        struct SomeStruct {
            one: u64,
            two: u64,
            inner: InnerStruct,
        }

        let s = SomeStruct {
            one: 012345,
            two: 543210,
            inner: InnerStruct { three: 3 },
        };

        let interpreted = Struct::from_bytes(&struct_def, None, unsafe { any_as_u8_slice(&s) })
            .expect("Failed to interpret struct");

        assert_eq!(interpreted.name, "some_struct");
        assert_eq!(interpreted.fields.len(), 3);

        assert_eq!(interpreted.fields[0].name, "one");
        assert_eq!(
            interpreted.fields[0].value.as_integer().expect("not int"),
            012345,
        );

        assert_eq!(interpreted.fields[1].name, "two");
        assert_eq!(
            interpreted.fields[1].value.as_integer().expect("not int"),
            543210
        );

        assert_eq!(interpreted.fields[2].name, "inner");
        let inner = interpreted.fields[2].value.as_struct().expect("not struct");
        assert_eq!(inner.name, "inner_struct");
        assert_eq!(inner.fields.len(), 1);
        assert_eq!(inner.fields[0].name, "three");
        assert_eq!(inner.fields[0].value.as_integer().expect("not int"), 3);
    }
    {
        use crate::btrfs::structs::Union as BtrfsUnion;

        let struct_def = BtrfsStruct {
            name: "some_struct",
            key_match: |_, _, _| false,
            fields: vec![BtrfsField {
                name: None,
                ty: BtrfsType::Union(BtrfsUnion {
                    name: "_anon_union",
                    fields: vec![
                        BtrfsField {
                            name: Some("one"),
                            ty: BtrfsType::U64,
                        },
                        BtrfsField {
                            name: None,
                            ty: BtrfsType::Struct(BtrfsStruct {
                                name: "_anon_struct",
                                key_match: |_, _, _| false,
                                fields: vec![
                                    BtrfsField {
                                        name: Some("two"),
                                        ty: BtrfsType::U64,
                                    },
                                    BtrfsField {
                                        name: Some("three"),
                                        ty: BtrfsType::U64,
                                    },
                                ],
                            }),
                        },
                    ],
                }),
            }],
        };

        #[derive(Clone, Copy)]
        #[repr(C, packed)]
        struct AnonStruct {
            two: u64,
            three: u64,
        }

        #[repr(C, packed)]
        union AnonUnion {
            one: u64,
            anon_struct: AnonStruct,
        }

        #[repr(C, packed)]
        struct SomeStruct {
            anon_union: AnonUnion,
        }

        let s = SomeStruct {
            anon_union: AnonUnion {
                anon_struct: AnonStruct {
                    two: 88888888888,
                    three: 7777777777777,
                },
            },
        };

        let interpreted = Struct::from_bytes(&struct_def, None, unsafe { any_as_u8_slice(&s) })
            .expect("Failed to interpret struct");

        assert_eq!(interpreted.name, "some_struct");
        assert_eq!(interpreted.fields.len(), 3);

        assert_eq!(interpreted.fields[0].name, "one");
        match interpreted.fields[0].value {
            Value::Integer(_) => (),
            _ => assert!(false, "Not integer field"),
        };

        assert_eq!(interpreted.fields[1].name, "two");
        assert_eq!(
            interpreted.fields[1].value.as_integer().expect("not int"),
            88888888888
        );

        assert_eq!(interpreted.fields[2].name, "three");
        assert_eq!(
            interpreted.fields[2].value.as_integer().expect("not int"),
            7777777777777
        );
    }
    {
        let struct_def = BtrfsStruct {
            name: "some_struct",
            key_match: |_, _, _| false,
            fields: vec![
                BtrfsField {
                    name: Some("name_1_len"),
                    ty: BtrfsType::U16,
                },
                BtrfsField {
                    name: Some("name_2_len"),
                    ty: BtrfsType::U16,
                },
                BtrfsField {
                    name: Some("name1"),
                    ty: BtrfsType::TrailingString("name_1_len"),
                },
                BtrfsField {
                    name: Some("name2"),
                    ty: BtrfsType::TrailingString("name_2_len"),
                },
            ],
        };

        #[repr(C, packed)]
        struct SomeStruct {
            name_1_len: u16,
            name_2_len: u16,
        }

        let s = SomeStruct {
            name_1_len: 5,
            name_2_len: 7,
        };

        let mut bytes = Vec::new();
        bytes.extend_from_slice(unsafe { any_as_u8_slice(&s) });
        bytes.extend_from_slice(&"hello".to_string().as_bytes());
        bytes.extend_from_slice(&"world12".to_string().as_bytes());

        let interpreted =
            Struct::from_bytes(&struct_def, None, &bytes).expect("Failed to interpret struct");

        assert_eq!(interpreted.name, "some_struct");
        assert_eq!(interpreted.fields.len(), 4);

        assert_eq!(interpreted.fields[0].name, "name_1_len");
        assert_eq!(
            interpreted.fields[0].value.as_integer().expect("not int"),
            5,
        );

        assert_eq!(interpreted.fields[1].name, "name_2_len");
        assert_eq!(
            interpreted.fields[1].value.as_integer().expect("not int"),
            7
        );

        assert_eq!(interpreted.fields[2].name, "name1");
        assert_eq!(
            interpreted.fields[2].value.as_string().expect("not string"),
            "hello"
        );

        assert_eq!(interpreted.fields[3].name, "name2");
        assert_eq!(
            interpreted.fields[3].value.as_string().expect("not string"),
            "world12"
        );
    }
}

#[test]
fn test_function_key() {
    let tests = vec![
        (
            r#"k = key(0, 1, 2, 3); print k.min_objectid;"#,
            "0\n".to_string(),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.min_type;"#,
            "1\n".to_string(),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.min_offset;"#,
            "2\n".to_string(),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.min_transid;"#,
            "3\n".to_string(),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.max_objectid;"#,
            format!("{}\n", u64::MAX),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.max_type;"#,
            format!("{}\n", u8::MAX),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.max_offset;"#,
            format!("{}\n", u64::MAX),
        ),
        (
            r#"k = key(0, 1, 2, 3); print k.max_transid;"#,
            format!("{}\n", u64::MAX),
        ),
        (
            r#"k = key(0, 1, 2, 3); k.min_type = 33; print k.min_type;"#,
            format!("{}\n", 33),
        ),
    ];

    use crate::lang::parse::parse;
    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);
        match eval.eval(&parse(input).expect("Failed to parse")) {
            EvalResult::Ok => (),
            _ => assert!(false, "Failed to eval input"),
        };
        assert_eq!(
            String::from_utf8(output).expect("Output not utf-8"),
            expected
        );
    }
}

#[test]
fn test_function_typeof() {
    let tests = vec![
        (
            r#"k = key(0, 1, 2, 3); print typeof(k);"#,
            "\"struct _btrfs_ioctl_search_key\"\n".to_string(),
        ),
        (r#"k = 1; print typeof(k);"#, "\"integer\"\n".to_string()),
        (
            r#"k = false; print typeof(k);"#,
            "\"boolean\"\n".to_string(),
        ),
        (r#"k = "str"; print typeof(k);"#, "\"string\"\n".to_string()),
    ];

    use crate::lang::parse::parse;
    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);
        match eval.eval(&parse(input).expect("Failed to parse")) {
            EvalResult::Ok => (),
            _ => assert!(false, "Failed to eval input"),
        };
        assert_eq!(
            String::from_utf8(output).expect("Output not utf-8"),
            expected
        );
    }
}

#[test]
fn test_array() {
    let tests = vec![
        (r#"print arr[0];"#, "3\n".to_string()),
        (r#"print arr[1];"#, "5\n".to_string()),
        (r#"print arr[2];"#, "\"asdf\"\n".to_string()),
        (r#"print len(arr);"#, "3\n".to_string()),
        (
            r#"arr += 99; print len(arr); print arr[3];"#,
            "4\n99\n".to_string(),
        ),
        (
            r#"for v in arr { print v; }"#,
            "3\n5\n\"asdf\"\n".to_string(),
        ),
    ];

    use crate::lang::parse::parse;
    for (input, expected) in tests {
        let mut output = Vec::new();
        let mut eval = Eval::new(&mut output, false);

        // Insert a test array
        eval.variables.insert(
            Identifier("arr".to_string()),
            Value::Array(Array {
                vec: vec![
                    Value::Integer(3),
                    Value::Integer(5),
                    Value::String("asdf".to_string()),
                ],
                is_hist: false,
            }),
        );

        match eval.eval(&parse(input).expect("Failed to parse")) {
            EvalResult::Ok => (),
            _ => assert!(false, "Failed to eval input"),
        };
        assert_eq!(
            String::from_utf8(output).expect("Output not utf-8"),
            expected
        );
    }
}
