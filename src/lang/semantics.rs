//! This module implements semantic analysis on the AST.
//!
//! Since btrd is dynamically typed semantic analysis only checks a few basic things, like variable
//! use-before-assigns, invalid statements, jump statements outside loops, etc.
use anyhow::{anyhow, bail, ensure, Result};

use crate::btrfs::definitions::STRUCTS;
use crate::lang::ast::*;
use crate::lang::variables::Variables;

pub struct SemanticAnalyzer {
    variables: Variables<()>,
    loop_depth: u32,
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self {
            variables: Variables::new(|_| (), |_| ()),
            loop_depth: 0,
        }
    }

    fn analyze_primary_expr(&mut self, expr: &PrimaryExpression) -> Result<()> {
        match expr {
            PrimaryExpression::Identifier(ident) => {
                let _ = self
                    .variables
                    .get(ident)
                    .ok_or_else(|| anyhow!("Unknown variable: {}", ident))?;

                Ok(())
            }
            PrimaryExpression::Constant(_) => Ok(()),
            PrimaryExpression::Str(_) => Ok(()),
            PrimaryExpression::Paren(expr) => self.analyze_expr(expr),
        }
    }

    fn analyze_binary_expr(&mut self, binop: &BinaryExpression) -> Result<()> {
        match binop {
            BinaryExpression::Plus(lhs, rhs)
            | BinaryExpression::Minus(lhs, rhs)
            | BinaryExpression::Multiply(lhs, rhs)
            | BinaryExpression::Divide(lhs, rhs)
            | BinaryExpression::Modulo(lhs, rhs)
            | BinaryExpression::BitOr(lhs, rhs)
            | BinaryExpression::BitAnd(lhs, rhs)
            | BinaryExpression::BitXor(lhs, rhs)
            | BinaryExpression::LeftShift(lhs, rhs)
            | BinaryExpression::RightShift(lhs, rhs)
            | BinaryExpression::LessThan(lhs, rhs)
            | BinaryExpression::LessThanEquals(lhs, rhs)
            | BinaryExpression::GreaterThan(lhs, rhs)
            | BinaryExpression::GreaterThanEquals(lhs, rhs)
            | BinaryExpression::Equals(lhs, rhs)
            | BinaryExpression::NotEquals(lhs, rhs)
            | BinaryExpression::LogicalOr(lhs, rhs)
            | BinaryExpression::LogicalAnd(lhs, rhs) => {
                self.analyze_expr(lhs)?;
                self.analyze_expr(rhs)?;

                Ok(())
            }
        }
    }

    fn analyze_unary_expr(&mut self, unop: &UnaryExpression) -> Result<()> {
        match unop {
            UnaryExpression::BitNot(e) | UnaryExpression::Not(e) | UnaryExpression::Minus(e) => {
                self.analyze_expr(&*e)
            }
            UnaryExpression::Cast(t, e) => match t {
                TypeSpecifier::Struct(ty) => match &**ty {
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        ident,
                    ))) => {
                        ensure!(
                            STRUCTS.iter().any(|s| s.name == ident),
                            "Unknown type: struct {}",
                            ident,
                        );

                        self.analyze_expr(e)?;

                        Ok(())
                    }
                    _ => bail!("Invalid type in type cast"),
                },
            },
        }
    }

    fn analyze_expr(&mut self, expr: &Expression) -> Result<()> {
        match expr {
            Expression::PrimaryExpression(p) => self.analyze_primary_expr(p),
            Expression::FieldAccess(expr, field) => {
                match &**field {
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(_))) => {
                    }
                    _ => bail!("Field in a field access must be an identifier"),
                };

                self.analyze_expr(expr)
            }
            Expression::ArrayIndex(expr, index) => {
                self.analyze_expr(expr)?;
                self.analyze_expr(index)?;

                Ok(())
            }
            Expression::FunctionCall(expr, args) => {
                self.analyze_expr(expr)?;
                for arg in args {
                    self.analyze_expr(arg)?;
                }

                Ok(())
            }
            Expression::BinaryExpression(b) => self.analyze_binary_expr(b),
            Expression::UnaryExpression(u) => self.analyze_unary_expr(u),
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
        self.analyze_expr(cond)?;
        self.analyze_stmts(true_body)?;
        self.analyze_stmts(false_body)?;

        Ok(())
    }

    fn analyze_for(
        &mut self,
        ident: &Expression,
        range: &Expression,
        stmts: &[Statement],
    ) -> Result<()> {
        let ident = match ident {
            Expression::PrimaryExpression(PrimaryExpression::Identifier(i)) => i,
            _ => bail!("Temporary variable in a for-loop must be an identifier"),
        };

        self.variables.insert(ident.clone(), ());

        self.analyze_expr(range)?;
        self.analyze_stmts(stmts)?;

        Ok(())
    }

    fn analyze_while(&mut self, cond: &Expression, stmts: &[Statement]) -> Result<()> {
        self.analyze_expr(cond)?;
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
                    self.variables.insert(ident.clone(), ());
                } else {
                    self.analyze_expr(lhs)?;
                }

                self.analyze_expr(rhs)?;

                Ok(())
            }
            Statement::BlockStatement(block) => self.analyze_block_stmt(block),
            Statement::JumpStatement(jump) => {
                ensure!(self.loop_depth > 0, "Cannot '{}' outside of a loop", jump);

                Ok(())
            }
            Statement::BuiltinStatement(builtin) => match builtin {
                BuiltinStatement::Help => Ok(()),
                BuiltinStatement::Quit => Ok(()),
                BuiltinStatement::Filesystem(expr) => match expr {
                    Expression::PrimaryExpression(PrimaryExpression::Str(_)) => Ok(()),
                    _ => bail!("'filesystem' builtin only takes string literal arguments"),
                },
                BuiltinStatement::Print(expr) => {
                    self.analyze_expr(expr)?;
                    Ok(())
                }
            },
            Statement::ExpressionStatement(expr) => {
                self.analyze_expr(expr)?;
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
        analyze(&stmts).expect("Semantic analysis failed")
    }
    {
        let prog = r#"
            for i in true {
                break;
                continue;
            }
        "#;
        let stmts = parse(prog);
        analyze(&stmts).expect("Semantic analysis failed");
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
            for i in true {
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
        analyze(&stmts).expect("Semantic analysis failed")
    }
    {
        let prog = r#"
            for i in true {
                inner_var = 3;
                inner_var2 = inner_var;
            }
        "#;
        let stmts = parse(prog);
        analyze(&stmts).expect("Semantic analysis failed");
    }
}

#[test]
fn test_builtin() {
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
        analyze(&stmts).expect("Semantic analysis failed")
    }
}

#[test]
fn test_type_cast() {
    {
        let prog = r#"
            (struct btrfs_key) 1;
        "#;
        let stmts = parse(prog);
        analyze(&stmts).expect("Semantic analysis failed");
    }
    {
        let prog = r#"
            (struct btrfs_keyz) 1;
        "#;
        let stmts = parse(prog);
        analyze(&stmts).expect_err("Semantic analysis passed");
    }
}
