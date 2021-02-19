//! This module implements semantic analysis on the AST.
//!
//! This module is responsible for ensuring that variables always retain the same type (btrd is a
//! strongly typed language) and expressions are valid. For example, ensuring that you cannot add a
//! bool and an integer.
//!
//! Since we type check here, evaluation can totally ignore types.
//!
//! WARNING: some of the implementation here is stubbed out waiting for builtin functions to be
//! implemented. The reason is that certain operations (ie field access and array indexing) only
//! makes sense when operating on btrfs data structures. btrd does not let the user define custom
//! structs or arrays.

use std::fmt;

use anyhow::{anyhow, bail, ensure, Result};

use crate::btrfs::definitions::{BTRFS_KEY, STRUCTS};
use crate::btrfs::structs::{Field, Type as BtrfsType};
use crate::lang::ast::*;
use crate::lang::eval::Eval;
use crate::lang::functions::Function;
use crate::lang::variables::Variables;

#[derive(PartialEq, Clone)]
pub enum Type {
    Integer,
    String,
    Boolean,
    Array(Box<Type>),
    /// Name of the struct
    Struct(String),
    Function(Function),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Integer => write!(f, "integer"),
            Type::String => write!(f, "string"),
            Type::Boolean => write!(f, "boolean"),
            Type::Array(t) => write!(f, "[{}]", *t),
            Type::Struct(name) => write!(f, "struct {}", name),
            Type::Function(func) => write!(f, "{}()", func),
        }
    }
}

impl From<BtrfsType> for Type {
    fn from(bty: BtrfsType) -> Self {
        match bty {
            BtrfsType::U8 | BtrfsType::U16 | BtrfsType::U32 | BtrfsType::U64 => Type::Integer,
            BtrfsType::TrailingString => Type::String,
            BtrfsType::Array(ty, _) => Type::Array(Box::new((*ty).into())),
            BtrfsType::Struct(s) => Type::Struct(s.name.to_string()),
            BtrfsType::Union(_) => panic!("Named unions are not supported"),
        }
    }
}

pub struct SemanticAnalyzer {
    variables: Variables<Type>,
    loop_depth: u32,
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self {
            variables: Variables::new(|_| Type::Integer, Type::Function),
            loop_depth: 0,
        }
    }

    fn eval_primary_expr_type(&self, expr: &PrimaryExpression, eval: &Eval) -> Result<Type> {
        let ty = match expr {
            PrimaryExpression::Identifier(ident) => self
                .variables
                .get(ident)
                .ok_or_else(|| anyhow!("Unknown variable: {}", ident))?
                .clone(),
            PrimaryExpression::Constant(c) => match c {
                Constant::Integer(_) => Type::Integer,
                Constant::Boolean(_) => Type::Boolean,
            },
            PrimaryExpression::Str(_) => Type::String,
            PrimaryExpression::Paren(expr) => self.eval_type(expr, eval)?,
        };

        Ok(ty)
    }

    fn eval_binop_type(&self, binop: &BinaryExpression, eval: &Eval) -> Result<Type> {
        let ty = match binop {
            BinaryExpression::Plus(lhs, rhs)
            | BinaryExpression::Minus(lhs, rhs)
            | BinaryExpression::Multiply(lhs, rhs)
            | BinaryExpression::Divide(lhs, rhs)
            | BinaryExpression::Modulo(lhs, rhs)
            | BinaryExpression::BitOr(lhs, rhs)
            | BinaryExpression::BitAnd(lhs, rhs)
            | BinaryExpression::BitXor(lhs, rhs)
            | BinaryExpression::LeftShift(lhs, rhs)
            | BinaryExpression::RightShift(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs, eval)?;
                let rhs_ty = self.eval_type(rhs, eval)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Integer, Type::Integer) => Type::Integer,
                    (_, _) => bail!(
                        "Cannot perform '{}' on '{}' and '{}'",
                        binop.op_str(),
                        lhs_ty,
                        rhs_ty
                    ),
                }
            }
            BinaryExpression::LessThan(lhs, rhs)
            | BinaryExpression::LessThanEquals(lhs, rhs)
            | BinaryExpression::GreaterThan(lhs, rhs)
            | BinaryExpression::GreaterThanEquals(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs, eval)?;
                let rhs_ty = self.eval_type(rhs, eval)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Integer, Type::Integer) => Type::Boolean,
                    (_, _) => bail!(
                        "Cannot perform '{}' on '{}' and '{}'",
                        binop.op_str(),
                        lhs_ty,
                        rhs_ty
                    ),
                }
            }
            BinaryExpression::Equals(lhs, rhs) | BinaryExpression::NotEquals(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs, eval)?;
                let rhs_ty = self.eval_type(rhs, eval)?;

                ensure!(
                    lhs_ty == rhs_ty,
                    "LHS ('{}') and RHS ('{}') of '{}' must be the same type",
                    lhs_ty,
                    rhs_ty,
                    binop.op_str()
                );
                Type::Boolean
            }
            BinaryExpression::LogicalOr(lhs, rhs) | BinaryExpression::LogicalAnd(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs, eval)?;
                let rhs_ty = self.eval_type(rhs, eval)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Boolean, Type::Boolean) => Type::Boolean,
                    (_, _) => bail!(
                        "LHS ('{}') and RHS ('{}') of '{}' must both be boolean type",
                        lhs_ty,
                        rhs_ty,
                        binop.op_str()
                    ),
                }
            }
        };

        Ok(ty)
    }

    fn eval_unary_type(&self, unop: &UnaryExpression, eval: &Eval) -> Result<Type> {
        match unop {
            UnaryExpression::BitNot(e) => {
                let ty = self.eval_type(&*e, eval)?;
                match ty {
                    t @ Type::Integer => Ok(t),
                    t => bail!("Cannot take binary not of type {}", t),
                }
            }
            UnaryExpression::Not(e) => {
                let ty = self.eval_type(&*e, eval)?;
                match ty {
                    // Integer conversion to boolean
                    Type::Integer => Ok(Type::Boolean),
                    t @ Type::Boolean => Ok(t),
                    t => bail!("Cannot take logical not of type: {}", t),
                }
            }
            UnaryExpression::Minus(e) => {
                let ty = self.eval_type(&*e, eval)?;
                match ty {
                    t @ Type::Integer => Ok(t),
                    t => bail!("Cannot take negative of type: {}", t),
                }
            }
        }
    }

    fn eval_type(&self, expr: &Expression, eval: &Eval) -> Result<Type> {
        match expr {
            Expression::PrimaryExpression(p) => self.eval_primary_expr_type(p, eval),
            Expression::FieldAccess(expr, field) => {
                let ident = match &**field {
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        ident,
                    ))) => ident,
                    _ => bail!("Field in a field access must be an identifier"),
                };

                let ty = self.eval_type(&*expr, eval)?;
                match ty {
                    Type::Struct(name) => {
                        let s = STRUCTS
                            .iter()
                            .find(|entry| entry.name == name)
                            .ok_or_else(|| anyhow!("Unknown struct '{}'", name))?;

                        fn find_field<'a>(name: &str, field: &'a Field) -> Option<&'a Field> {
                            if let Some(n) = field.name {
                                if n == name {
                                    return Some(field);
                                }
                            }

                            match &field.ty {
                                BtrfsType::Struct(s) => {
                                    for f in &s.fields {
                                        let res = find_field(name, f);
                                        if res.is_some() {
                                            return res;
                                        }
                                    }
                                }
                                BtrfsType::Union(s) => {
                                    for f in &s.fields {
                                        let res = find_field(name, f);
                                        if res.is_some() {
                                            return res;
                                        }
                                    }
                                }
                                _ => (),
                            };

                            None
                        }

                        let field = s
                            .fields
                            .iter()
                            .find_map(|f| find_field(&ident, f))
                            .ok_or_else(|| {
                                anyhow!("Unknown field '{}' in struct '{}'", ident, s.name)
                            })?;

                        Ok(field.ty.clone().into())
                    }
                    _ => bail!("Cannot access field '{}' on type '{}'", ident, ty),
                }
            }
            Expression::ArrayIndex(expr, index) => {
                let expr_ty = self.eval_type(expr, eval)?;
                let index_ty = self.eval_type(index, eval)?;

                match index_ty {
                    Type::Integer => (),
                    t => bail!("Array index must be 'integer' type, found '{}'", t),
                };

                match expr_ty {
                    Type::Array(t) => Ok(*t),
                    t => bail!(
                        "Array index can only be used on type 'array', found '{}'",
                        t
                    ),
                }
            }
            Expression::FunctionCall(expr, args) => {
                let expr_ty = self.eval_type(expr, eval)?;
                let mut args_ty = Vec::with_capacity(args.len());
                for arg in args {
                    args_ty.push(self.eval_type(arg, eval)?);
                }

                match expr_ty {
                    Type::Function(f) => match f {
                        Function::Key => {
                            ensure!(args_ty.len() == 4, "'{}' requires 4 arguments", expr_ty);
                            for i in 0..args_ty.len() {
                                ensure!(
                                    args_ty[i] == Type::Integer,
                                    "'{}'s argument {} must be '{}'",
                                    expr_ty,
                                    i,
                                    Type::Integer
                                );
                            }

                            unimplemented!();
                        }
                        Function::Search => {
                            unimplemented!();
                        }
                    },
                    t => bail!("Expected function for function call, found: '{}'", t),
                }
            }
            Expression::BinaryExpression(b) => self.eval_binop_type(b, eval),
            Expression::UnaryExpression(u) => self.eval_unary_type(u, eval),
        }
    }

    fn analyze_stmts(&mut self, stmts: &[Statement], eval: &Eval) -> Result<()> {
        for stmt in stmts {
            self.analyze_stmt(stmt, eval)?;
        }

        Ok(())
    }

    fn analyze_if(
        &mut self,
        cond: &Expression,
        true_body: &[Statement],
        false_body: &[Statement],
        eval: &Eval,
    ) -> Result<()> {
        match self.eval_type(cond, eval)? {
            Type::Boolean => (),
            _ => bail!("'if' condition must be a boolean type"),
        };

        self.analyze_stmts(true_body, eval)?;
        self.analyze_stmts(false_body, eval)?;

        Ok(())
    }

    fn analyze_for(
        &mut self,
        _ident: &Expression,
        _range: &Expression,
        _stmts: &[Statement],
        _eval: &Eval,
    ) -> Result<()> {
        bail!("For loops are currently unimplemented");

        // Check that temporary variable is an identifier

        // Add temporary variable to variable tracker

        // Check expression is a range

        // self.analyze_stmts(stmts)?;
    }

    fn analyze_while(&mut self, cond: &Expression, stmts: &[Statement], eval: &Eval) -> Result<()> {
        match self.eval_type(cond, eval)? {
            Type::Boolean => (),
            _ => bail!("'while' condition must be a boolean type"),
        };

        self.analyze_stmts(stmts, eval)?;

        Ok(())
    }

    fn analyze_block_stmt(&mut self, block: &BlockStatement, eval: &Eval) -> Result<()> {
        match block {
            BlockStatement::If(cond, true_body, false_body) => {
                self.variables.push_scope();
                let ret = self.analyze_if(cond, true_body, false_body, eval);
                self.variables.pop_scope();

                ret
            }
            BlockStatement::While(cond, stmts) => {
                self.loop_depth += 1;
                self.variables.push_scope();

                let ret = self.analyze_while(cond, stmts, eval);

                self.loop_depth -= 1;
                self.variables.pop_scope();

                ret
            }
            BlockStatement::For(ident, range, stmts) => {
                self.loop_depth += 1;
                self.variables.push_scope();

                let ret = self.analyze_for(ident, range, stmts, eval);

                self.loop_depth -= 1;
                self.variables.pop_scope();

                ret
            }
        }
    }

    fn analyze_stmt(&mut self, stmt: &Statement, eval: &Eval) -> Result<()> {
        match stmt {
            Statement::AssignStatement(lhs, rhs) => {
                if let Expression::PrimaryExpression(PrimaryExpression::Identifier(ident)) = lhs {
                    let rhs_type = self.eval_type(rhs, eval)?;
                    if let Some(lhs_type) = self.variables.get(ident) {
                        ensure!(
                            lhs_type == &rhs_type,
                            "Cannot assign type '{}' to '{}' (which is type '{}')",
                            rhs_type,
                            ident,
                            lhs_type
                        );
                    } else {
                        self.variables.insert(ident.clone(), rhs_type);
                    }

                    Ok(())
                } else {
                    bail!("Must assign value to an identifier");
                }
            }
            Statement::BlockStatement(block) => self.analyze_block_stmt(block, eval),
            Statement::JumpStatement(jump) => {
                ensure!(self.loop_depth > 0, "Cannot '{}' outside of a loop", jump);

                Ok(())
            }
            Statement::BuiltinStatement(builtin) => {
                match builtin {
                    BuiltinStatement::Help => Ok(()),
                    BuiltinStatement::Quit => Ok(()),
                    BuiltinStatement::Filesystem(expr) => match expr {
                        Expression::PrimaryExpression(PrimaryExpression::Str(_)) => Ok(()),
                        _ => bail!("'filesystem' builtin only takes string literal arguments"),
                    },
                    BuiltinStatement::Print(expr) => {
                        // Check that expression is valid -- `print` can print any type
                        let _ = self.eval_type(expr, eval)?;
                        Ok(())
                    }
                }
            }
            Statement::ExpressionStatement(expr) => {
                // Just need to make sure the expression is valid
                let _ = self.eval_type(expr, eval)?;
                Ok(())
            }
        }
    }

    pub fn analyze(&mut self, stmts: &[Statement], eval: &Eval) -> Result<()> {
        for stmt in stmts {
            self.analyze_stmt(stmt, eval)?;
        }

        Ok(())
    }
}

#[cfg(test)]
fn analyze(stmts: &[Statement]) -> Result<()> {
    SemanticAnalyzer::new().analyze(stmts)
}

#[cfg(test)]
fn parse(prog: &str) -> Vec<Statement> {
    use crate::lang::parse::parse;
    parse(prog).unwrap()
}

#[test]
fn test_jump_outside_loop() {
    {
        let prog = r#"
            break;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            continue;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            while true {
                break;
                continue;
            }
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}

#[test]
fn test_assign_var_different_types() {
    {
        let prog = r#"
            var = 1;
            var = true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            var = 1;
            var = 2;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}

#[test]
fn test_variable_scope() {
    {
        let prog = r#"
            while true {
                inner_var = 3;
            }
            outer_var = inner_var;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            while true {
                inner_var = 3;
                inner_var = 4;
            }
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}

#[test]
fn test_unops() {
    {
        let prog = r#"
            !"str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            ~"asdf";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            ~true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            -"str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            -true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            !1;
            !!1;
            !!!!!5;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
    {
        let prog = r#"
            ~1;
            ~~1;
            ~~~5;
            -~~~5;
            --~~~5;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
    {
        let prog = r#"
            -1;
            --1;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}

#[test]
fn test_binops() {
    {
        let prog = r#"
            true + 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            3 - false;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            "string" * false;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            "string" / 1234;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            "string" % 1234;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            "string" == 1234;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            false != 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            false && 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            false || 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            false | 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            3 & true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            3 ^ true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 << "asdf";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            true >> 3;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 < "str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 > "str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 >= "str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 <= "str";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            1 + 3;
            1 - 4;
            1 - 2 - 3;
            1 * 3 * 4;
            5 / 6;
            3 % 3 % 2;
            2 == 2;
            true != false;
            true == true;
            true && false;
            true || !!3;
            2 | 3;
            2 & 3;
            2 ^ 4;
            1 << 2 >> 3;
            3 >> 5;
            3 < 4;
            3 > 4;
            3 >= 4;
            3 <= 4;
            (5 < 3) || false;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}

#[test]
fn test_builtin() {
    {
        let prog = r#"
            print 3 + true;
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_err());
    }
    {
        let prog = r#"
            help;
            quit;
            filesystem "/mnt/asdf/waa";
            print 3;
            print true;
            print "asdf";
        "#;
        let stmts = parse(prog);
        assert!(analyze(&stmts).is_ok());
    }
}
