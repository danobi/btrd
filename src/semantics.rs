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

use crate::ast::*;
use crate::variables::Variables;

#[derive(PartialEq, Clone)]
pub struct IntegerType {}

impl fmt::Display for IntegerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "integer")
    }
}

#[derive(PartialEq, Clone)]
pub struct StringType {}

impl fmt::Display for StringType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "string")
    }
}

#[derive(PartialEq, Clone)]
pub struct BooleanType {}

impl fmt::Display for BooleanType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "boolean")
    }
}

#[derive(PartialEq, Clone)]
pub enum Type {
    Integer(IntegerType),
    String(StringType),
    Boolean(BooleanType),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Integer(t) => write!(f, "{}", t),
            Type::String(t) => write!(f, "{}", t),
            Type::Boolean(t) => write!(f, "{}", t),
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
            variables: Variables::new(),
            loop_depth: 0,
        }
    }

    fn eval_primary_expr_type(&self, expr: &PrimaryExpression) -> Result<Type> {
        let ty = match expr {
            PrimaryExpression::Identifier(ident) => self
                .variables
                .get(ident)
                .ok_or_else(|| anyhow!("Unknown variable: {}", ident))?
                .clone(),
            PrimaryExpression::Constant(c) => match c {
                Constant::Integer(_) => Type::Integer(IntegerType {}),
                Constant::Boolean(_) => Type::Boolean(BooleanType {}),
            },
            PrimaryExpression::Str(_) => Type::String(StringType {}),
            PrimaryExpression::Paren(expr) => self.eval_type(expr)?,
        };

        Ok(ty)
    }

    fn eval_binop_type(&self, binop: &BinaryExpression) -> Result<Type> {
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
                let lhs_ty = self.eval_type(lhs)?;
                let rhs_ty = self.eval_type(rhs)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Integer(_), Type::Integer(_)) => Type::Integer(IntegerType {}),
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
                let lhs_ty = self.eval_type(lhs)?;
                let rhs_ty = self.eval_type(rhs)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Integer(_), Type::Integer(_)) => Type::Boolean(BooleanType {}),
                    (_, _) => bail!(
                        "Cannot perform '{}' on '{}' and '{}'",
                        binop.op_str(),
                        lhs_ty,
                        rhs_ty
                    ),
                }
            }
            BinaryExpression::Equals(lhs, rhs) | BinaryExpression::NotEquals(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs)?;
                let rhs_ty = self.eval_type(rhs)?;

                ensure!(
                    lhs_ty == rhs_ty,
                    "LHS ('{}') and RHS ('{}') of '{}' must be the same type",
                    lhs_ty,
                    rhs_ty,
                    binop.op_str()
                );
                Type::Boolean(BooleanType {})
            }
            BinaryExpression::LogicalOr(lhs, rhs) | BinaryExpression::LogicalAnd(lhs, rhs) => {
                let lhs_ty = self.eval_type(lhs)?;
                let rhs_ty = self.eval_type(rhs)?;

                match (&lhs_ty, &rhs_ty) {
                    (Type::Boolean(_), Type::Boolean(_)) => Type::Boolean(BooleanType {}),
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

    fn eval_unary_type(&self, unop: &UnaryExpression) -> Result<Type> {
        match unop {
            UnaryExpression::BitNot(e) => {
                let ty = self.eval_type(&*e)?;
                match ty {
                    t @ Type::Integer(_) => Ok(t),
                    t => bail!("Cannot take binary not of type {}", t),
                }
            }
            UnaryExpression::Not(e) => {
                let ty = self.eval_type(&*e)?;
                match ty {
                    // Integer conversion to boolean
                    Type::Integer(_) => Ok(Type::Boolean(BooleanType {})),
                    t @ Type::Boolean(_) => Ok(t),
                    t => bail!("Cannot take logical not of type: {}", t),
                }
            }
            UnaryExpression::Minus(e) => {
                let ty = self.eval_type(&*e)?;
                match ty {
                    t @ Type::Integer(_) => Ok(t),
                    t => bail!("Cannot take negative of type: {}", t),
                }
            }
        }
    }

    fn eval_type(&self, expr: &Expression) -> Result<Type> {
        match expr {
            Expression::PrimaryExpression(p) => self.eval_primary_expr_type(p),
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
            Expression::BinaryExpression(b) => self.eval_binop_type(b),
            Expression::UnaryExpression(u) => self.eval_unary_type(u),
        }
    }

    fn analyze_stmts(&mut self, stmts: &[Statement]) -> Result<()> {
        for stmt in stmts {
            self.analyze_stmt(stmt)?;
        }

        Ok(())
    }

    fn analyze_if(
        &mut self,
        cond: &Expression,
        true_body: &[Statement],
        false_body: &[Statement],
    ) -> Result<()> {
        match self.eval_type(cond)? {
            Type::Boolean(_) => (),
            _ => bail!("'if' condition must be a boolean type"),
        };

        self.analyze_stmts(true_body)?;
        self.analyze_stmts(false_body)?;

        Ok(())
    }

    fn analyze_for(
        &mut self,
        _ident: &Expression,
        _range: &Expression,
        _stmts: &[Statement],
    ) -> Result<()> {
        bail!("For loops are currently unimplemented");

        // Check that temporary variable is an identifier

        // Add temporary variable to variable tracker

        // Check expression is a range

        // self.analyze_stmts(stmts)?;
    }

    fn analyze_while(&mut self, cond: &Expression, stmts: &[Statement]) -> Result<()> {
        match self.eval_type(cond)? {
            Type::Boolean(_) => (),
            _ => bail!("'while' condition must be a boolean type"),
        };

        self.analyze_stmts(stmts)?;

        Ok(())
    }

    fn analyze_block_stmt(&mut self, block: &BlockStatement) -> Result<()> {
        match block {
            BlockStatement::If(cond, true_body, false_body) => {
                self.variables.push_scope();
                let ret = self.analyze_if(cond, true_body, false_body);
                self.variables.pop_scope();

                ret
            }
            BlockStatement::While(cond, stmts) => {
                self.loop_depth += 1;
                self.variables.push_scope();

                let ret = self.analyze_while(cond, stmts);

                self.loop_depth -= 1;
                self.variables.pop_scope();

                ret
            }
            BlockStatement::For(ident, range, stmts) => {
                self.loop_depth += 1;
                self.variables.push_scope();

                let ret = self.analyze_for(ident, range, stmts);

                self.loop_depth -= 1;
                self.variables.pop_scope();

                ret
            }
        }
    }

    fn analyze_stmt(&mut self, stmt: &Statement) -> Result<()> {
        match stmt {
            Statement::AssignStatement(lhs, rhs) => {
                if let Expression::PrimaryExpression(PrimaryExpression::Identifier(ident)) = lhs {
                    let rhs_type = self.eval_type(rhs)?;
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
            Statement::BlockStatement(block) => self.analyze_block_stmt(block),
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
                        let _ = self.eval_type(expr)?;
                        Ok(())
                    }
                }
            }
            Statement::ExpressionStatement(expr) => {
                // Just need to make sure the expression is valid
                let _ = self.eval_type(expr)?;
                Ok(())
            }
        }
    }

    pub fn analyze(&mut self, stmts: &[Statement]) -> Result<()> {
        for stmt in stmts {
            self.analyze_stmt(stmt)?;
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
    use crate::parse::parse;
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
