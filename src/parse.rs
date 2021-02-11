//! This module implements btrd's domain specific language.
//!
//! The DSL is defined as a PEG (https://en.wikipedia.org/wiki/Parsing_expression_grammar)
//! and by definition unambiguous. If you're not familiar with PEGs, you can think of it
//! as a formalization for the very pragmatic recursive descent parser.
//!
//! Developer notes:
//!
//! * A PEG is order sensitive. If you're having trouble getting your rules to parse, check
//!   that keywords/tokens are parsed before identifiers. For example, ensure that `<=` is parsed
//!   before `<`, otherwise the parser will take `<` and be consfused when it sees the `=`.
//!   Likewise, ensure that tokens like `help` are parsed by a rule before the identifier rule is
//!   kicked in.
//!
//! * PEGs may not have left recursion (left recursion manifests as an infinite loop that
//!   eventually blows the stack). For example, this rule is not valid:
//!
//!     expr <- expr '*' expr
//!
//!   because PEGs are greedy and always try to take the first match.
//!
//! * To implement operator precedence, this parser uses a "precedence ladder" (a term I'm making
//!   up and not to be confused with a "precedence climber"). Lower precedence operations are
//!   "higher up" on the parser so they bind later than the higher precedence operators. For
//!   example, because `||` is lower precedence than `&&`, the `||` production rule is before
//!   the `&&` production rule. That way, if `&&` is in the lhs or rhs of `||`, the `&&` has a
//!   chance to bind to further operands before `||`.
//!

use std::char::decode_utf16;
use std::char::REPLACEMENT_CHARACTER;
use std::collections::VecDeque;
use std::iter::FromIterator;
use std::str::FromStr;

use pom::parser::{call, end, is_a, list, none_of, one_of, sym, tag, Parser};

use crate::ast::*;

/// Macro to left fold a series of binary expressions
///
/// Left fold creates left-to-right associativity, ie:
///     1 + 2 + 3 + 4 => ((1 + 2) + 3) + 4
macro_rules! left_fold_binop {
    ($binop_ty: expr, $lhs: expr, $rest: expr) => {{
        let binop_create_fn =
            |_op, e, ee| -> BinaryExpression { $binop_ty(Box::new(e), Box::new(ee)) };

        // Assign dummy operators b/c we already know the binop type and ignore the operator
        // argument in `binop_create_fn`
        let rest = $rest
            .drain(0..)
            .map(|e| ("", e))
            .collect::<Vec<(&str, Expression)>>();

        left_fold_binop_multiop!(binop_create_fn, $lhs, rest)
    }};
}

/// Same as `left_fold_binop` except intead of taking one binop type, takes a function,
/// `binop_create_fn`, that creates an `BinaryExpression` based on the operator
macro_rules! left_fold_binop_multiop {
    ($binop_create_fn: expr, $lhs: expr, $rest: expr) => {{
        let func = || -> Expression {
            // Each entry is the deque is a tuple of (operation, expression)
            let mut deque: VecDeque<(&str, Expression)> = $rest.into();

            let mut expr = $lhs;
            while let Some((op, e)) = deque.pop_front() {
                expr = Expression::BinaryExpression($binop_create_fn(op, expr, e));
            }

            expr
        };

        func()
    }};
}

fn space<'a>() -> Parser<'a, char, ()> {
    one_of(" \t\r\n").repeat(0..).discard()
}

fn string<'a>() -> Parser<'a, char, Expression> {
    let special_char = sym('\\')
        | sym('/')
        | sym('"')
        | sym('b').map(|_| '\x08')
        | sym('f').map(|_| '\x0C')
        | sym('n').map(|_| '\n')
        | sym('r').map(|_| '\r')
        | sym('t').map(|_| '\t');
    let escape_sequence = sym('\\') * special_char;
    let char_string = (none_of("\\\"") | escape_sequence)
        .repeat(1..)
        .map(String::from_iter);
    let utf16_char = tag("\\u")
        * is_a(|c: char| c.is_digit(16))
            .repeat(4)
            .map(String::from_iter)
            .convert(|digits| u16::from_str_radix(&digits, 16));
    let utf16_string = utf16_char.repeat(1..).map(|chars| {
        decode_utf16(chars)
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .collect::<String>()
    });
    let string = sym('"') * (char_string | utf16_string).repeat(0..) - sym('"');

    string
        .map(|strings| strings.concat())
        .map(|s| Expression::PrimaryExpression(PrimaryExpression::Str(s)))
}

fn constant<'a>() -> Parser<'a, char, Expression> {
    let integer = (one_of("123456789") - one_of("0123456789").repeat(0..)) | sym('0');
    let number = (sym('-').opt() + integer)
        .collect()
        .map(String::from_iter)
        .convert(|s| i64::from_str(&s));
    let constant = number.map(Constant::Integer)
        | tag("true").map(|_| Constant::Boolean(true))
        | tag("false").map(|_| Constant::Boolean(false));

    constant.map(|c| Expression::PrimaryExpression(PrimaryExpression::Constant(c)))
}

fn ident<'a>() -> Parser<'a, char, Expression> {
    (is_a(|c: char| c.is_ascii_alphabetic() || c == '_')
        + is_a(|c: char| c.is_ascii_alphanumeric()).repeat(0..))
    .collect()
    .map(String::from_iter)
    .map(Identifier)
    .map(|i| Expression::PrimaryExpression(PrimaryExpression::Identifier(i)))
}

fn primary_expr<'a>() -> Parser<'a, char, Expression> {
    let paren = (sym('(') * call(expr) - space() - sym(')'))
        .map(|e| Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(e))));

    constant() | ident() | string() | paren
}

fn postfix_expr<'a>() -> Parser<'a, char, Expression> {
    enum PostfixOp {
        FunctionCall(Vec<Expression>),
        ArrayIndex(Expression),
        FieldAccess(Expression),
    }

    let arg_list = list(call(expr), space() * sym(','));
    let function_call = (sym('(') * arg_list - space() - sym(')')).map(PostfixOp::FunctionCall);
    let array_index = (sym('[') * call(expr) - space() - sym(']')).map(PostfixOp::ArrayIndex);
    let field_access = (sym('.') * ident()).map(PostfixOp::FieldAccess);
    let parser =
        call(primary_expr) + (space() * (function_call | array_index | field_access)).repeat(0..);

    // NB: postfix operators are left-to-right associativity, so fold-left
    parser.map(|(primary, rest)| {
        let mut rest: VecDeque<PostfixOp> = rest.into();
        let mut expr = primary;
        while let Some(op) = rest.pop_front() {
            match op {
                PostfixOp::FunctionCall(args) => {
                    expr = Expression::FunctionCall(Box::new(expr), args)
                }
                PostfixOp::ArrayIndex(index) => {
                    expr = Expression::ArrayIndex(Box::new(expr), Box::new(index))
                }
                PostfixOp::FieldAccess(ident) => {
                    expr = Expression::FieldAccess(Box::new(expr), Box::new(ident))
                }
            }
        }

        expr
    })
}

fn unary_expr<'a>() -> Parser<'a, char, Expression> {
    let ops = tag("~") | tag("!") | tag("-");
    let bnot_not_minus = (ops - space()).repeat(0..) - space() + call(postfix_expr);

    // NB: unary expression are right-to-left associativity, so fold-right
    bnot_not_minus.map(|(mut ops, expr)| {
        let mut expr = expr;
        while let Some(op) = ops.pop() {
            match op {
                "~" => expr = Expression::UnaryExpression(UnaryExpression::BitNot(Box::new(expr))),
                "!" => expr = Expression::UnaryExpression(UnaryExpression::Not(Box::new(expr))),
                "-" => expr = Expression::UnaryExpression(UnaryExpression::Minus(Box::new(expr))),
                _ => panic!("Unhandled unary operator: {}", op),
            }
        }

        expr
    })
}

fn mult_expr<'a>() -> Parser<'a, char, Expression> {
    let ops = tag("*") | tag("/") | tag("%");
    let mult_div_mod = call(unary_expr) + (space() * ops - space() + call(unary_expr)).repeat(0..);

    mult_div_mod.map(|(lhs, rest)| {
        let binop_create_fn = |op, lhs, rhs| match op {
            "*" => BinaryExpression::Multiply(Box::new(lhs), Box::new(rhs)),
            "/" => BinaryExpression::Divide(Box::new(lhs), Box::new(rhs)),
            "%" => BinaryExpression::Modulo(Box::new(lhs), Box::new(rhs)),
            _ => panic!("Unhandled mult operator: {}", op),
        };

        left_fold_binop_multiop!(binop_create_fn, lhs, rest)
    })
}

fn add_expr<'a>() -> Parser<'a, char, Expression> {
    let ops = tag("+") | tag("-");
    let plus_minus = call(mult_expr) + (space() * ops - space() + call(mult_expr)).repeat(0..);

    plus_minus.map(|(lhs, rest)| {
        let binop_create_fn = |op, lhs, rhs| match op {
            "+" => BinaryExpression::Plus(Box::new(lhs), Box::new(rhs)),
            "-" => BinaryExpression::Minus(Box::new(lhs), Box::new(rhs)),
            _ => panic!("Unhandled addition operator: {}", op),
        };

        left_fold_binop_multiop!(binop_create_fn, lhs, rest)
    })
}

fn shift_expr<'a>() -> Parser<'a, char, Expression> {
    let ops = tag("<<") | tag(">>");
    let lsh_rsh = call(add_expr) + (space() * ops - space() + call(add_expr)).repeat(0..);

    lsh_rsh.map(|(lhs, rest)| {
        let binop_create_fn = |op, lhs, rhs| match op {
            "<<" => BinaryExpression::LeftShift(Box::new(lhs), Box::new(rhs)),
            ">>" => BinaryExpression::RightShift(Box::new(lhs), Box::new(rhs)),
            _ => panic!("Unhandled shift operator: {}", op),
        };

        left_fold_binop_multiop!(binop_create_fn, lhs, rest)
    })
}

fn relation_expr<'a>() -> Parser<'a, char, Expression> {
    // NB: order matters for PEGs -- must keep the longer symbol first if the latter is a substring
    //
    // ie. `<=` must be before `<` otherwise `<` will be parsed
    let ops = tag("<=") | tag("<") | tag(">=") | tag(">");
    let lt_lte_gt_gte = call(shift_expr) + (space() * ops - space() + call(shift_expr)).repeat(0..);

    lt_lte_gt_gte.map(|(lhs, rest)| {
        let binop_create_fn = |op, lhs, rhs| match op {
            "<" => BinaryExpression::LessThan(Box::new(lhs), Box::new(rhs)),
            "<=" => BinaryExpression::LessThanEquals(Box::new(lhs), Box::new(rhs)),
            ">" => BinaryExpression::GreaterThan(Box::new(lhs), Box::new(rhs)),
            ">=" => BinaryExpression::GreaterThanEquals(Box::new(lhs), Box::new(rhs)),
            _ => panic!("Unhandled relational operator: {}", op),
        };

        left_fold_binop_multiop!(binop_create_fn, lhs, rest)
    })
}

/// NB: equality expressions cannot be chained (eg `1 == 2 == false`)
fn eq_expr<'a>() -> Parser<'a, char, Expression> {
    let ops = tag("==") | tag("!=");
    let eq_neq = call(relation_expr) + (space() * ops - space() + call(relation_expr)).opt();

    eq_neq.map(|(lhs, rhs)| {
        if let Some((op, rhs)) = rhs {
            match op {
                "==" => Expression::BinaryExpression(BinaryExpression::Equals(
                    Box::new(lhs),
                    Box::new(rhs),
                )),
                "!=" => Expression::BinaryExpression(BinaryExpression::NotEquals(
                    Box::new(lhs),
                    Box::new(rhs),
                )),
                _ => panic!("Unhandled equality operator: {}", op),
            }
        } else {
            lhs
        }
    })
}

fn bit_and_expr<'a>() -> Parser<'a, char, Expression> {
    let band = call(eq_expr) + (space() * sym('&') * space() * call(eq_expr)).repeat(0..);
    band.map(|(lhs, mut rhs)| left_fold_binop!(BinaryExpression::BitAnd, lhs, rhs))
}

fn bit_xor_expr<'a>() -> Parser<'a, char, Expression> {
    let bxor = call(bit_and_expr) + (space() * sym('^') * space() * call(bit_and_expr)).repeat(0..);
    bxor.map(|(lhs, mut rhs)| left_fold_binop!(BinaryExpression::BitXor, lhs, rhs))
}

fn bit_or_expr<'a>() -> Parser<'a, char, Expression> {
    let bor = call(bit_xor_expr) + (space() * sym('|') * space() * call(bit_xor_expr)).repeat(0..);
    bor.map(|(lhs, mut rhs)| left_fold_binop!(BinaryExpression::BitOr, lhs, rhs))
}

fn and_expr<'a>() -> Parser<'a, char, Expression> {
    let land = call(bit_or_expr) + (space() * tag("&&") * space() * call(bit_or_expr)).repeat(0..);
    land.map(|(lhs, mut rhs)| left_fold_binop!(BinaryExpression::LogicalAnd, lhs, rhs))
}

fn or_expr<'a>() -> Parser<'a, char, Expression> {
    let lor = call(and_expr) + (space() * tag("||") * space() * call(and_expr)).repeat(0..);
    lor.map(|(lhs, mut rhs)| left_fold_binop!(BinaryExpression::LogicalOr, lhs, rhs))
}

/// Parse an expression
///
/// Consumes leading whitespace
fn expr<'a>() -> Parser<'a, char, Expression> {
    space() * or_expr()
}

fn assign_stmt<'a>() -> Parser<'a, char, Statement> {
    let assignment = expr() - space() - sym('=') + expr();
    assignment.map(|(lhs, rhs)| Statement::AssignStatement(lhs, rhs))
}

fn if_else_stmt<'a>() -> Parser<'a, char, Statement> {
    let if_stmt = tag("if") * expr() - space() - sym('{') + call(stmts) - space() - sym('}');
    let else_stmt = space() * tag("else") * space() * sym('{') * call(stmts) - space() - sym('}');
    (if_stmt + else_stmt.opt()).map(|((cond, true_body), false_body)| {
        Statement::BlockStatement(BlockStatement::If(
            cond,
            true_body,
            false_body.unwrap_or_else(Vec::new),
        ))
    })
}

fn block_stmt<'a>() -> Parser<'a, char, Statement> {
    let while_stmt =
        (tag("while") * expr() - space() - sym('{') + call(stmts) - space() - sym('}'))
            .map(|(cond, body)| Statement::BlockStatement(BlockStatement::While(cond, body)));
    let for_stmt =
        (tag("for") * space() * ident() - space() - tag("in") + expr() - space() - sym('{')
            + call(stmts)
            - space()
            - sym('}'))
        .map(|((ident, range), body)| {
            Statement::BlockStatement(BlockStatement::For(ident, range, body))
        });

    if_else_stmt() | while_stmt | for_stmt
}

fn jump_stmt<'a>() -> Parser<'a, char, Statement> {
    tag("break").map(|_| Statement::JumpStatement(JumpStatement::Break))
        | tag("continue").map(|_| Statement::JumpStatement(JumpStatement::Continue))
}

fn builtin_stmt<'a>() -> Parser<'a, char, Statement> {
    let help = tag("help").map(|_| Statement::BuiltinStatement(BuiltinStatement::Help));
    let quit = tag("quit").map(|_| Statement::BuiltinStatement(BuiltinStatement::Quit));
    let filesystem_stmt = (tag("filesystem") * space() * string())
        .map(|expr| Statement::BuiltinStatement(BuiltinStatement::Filesystem(expr)));
    let print_stmt = tag("print")
        * expr().map(|expr| Statement::BuiltinStatement(BuiltinStatement::Print(expr)));

    filesystem_stmt | print_stmt | help | quit
}

fn expr_stmt<'a>() -> Parser<'a, char, Statement> {
    expr().map(Statement::ExpressionStatement)
}

/// Parse a statment
///
/// Consumes leading whitespace
fn stmt<'a>() -> Parser<'a, char, Statement> {
    // NB: keywords must come first otherwise they may be parsed as identifiers
    let stmt_semicolon =
        (builtin_stmt() | jump_stmt() | assign_stmt() | expr_stmt()) - space() - sym(';');

    space() * (stmt_semicolon | block_stmt())
}

/// Parse a series of statements
///
/// Consumes leading and trailing whitespace
fn stmts<'a>() -> Parser<'a, char, Vec<Statement>> {
    stmt().repeat(0..)
}

pub fn parse(input: &str) -> pom::Result<Vec<Statement>> {
    let input: Vec<char> = input.chars().collect();
    let program = stmts() - end();
    let stmts = program.parse(&input)?;

    Ok(stmts)
}

#[test]
fn test_string() {
    {
        let data = vec![
            (r#""hello world""#, "hello world"),
            (r#""hello world\n""#, "hello world\n"),
            (r#""hello world\t""#, "hello world\t"),
            (r#""   hello world " "#, "   hello world "),
            (r#""❤""#, "❤"),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(
                string().parse(&input),
                Ok(Expression::PrimaryExpression(PrimaryExpression::Str(
                    expected.to_string()
                )))
            );
        }
    }
    {
        let data = vec![r#"hello world""#, r#"hello world"#, r#"23423s"#];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(string().parse(&input).is_err());
        }
    }
}

#[test]
fn test_constant() {
    {
        let data = vec![
            ("0", Constant::Integer(0)),
            ("-0", Constant::Integer(0)),
            ("2342", Constant::Integer(2342)),
            ("-2342", Constant::Integer(-2342)),
            ("false", Constant::Boolean(false)),
            ("true", Constant::Boolean(true)),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(
                constant().parse(&input),
                Ok(Expression::PrimaryExpression(PrimaryExpression::Constant(
                    expected
                )))
            );
        }
    }
    {
        let data = vec![("abc"), ("c3"), ("-----"), ("+234")];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(constant().parse(&input).is_err());
        }
    }
}

#[test]
fn test_primary_expr() {
    {
        let data = vec![
            (
                "asdf",
                Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                    "asdf".to_string(),
                ))),
            ),
            (
                "_var1",
                Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                    "_var1".to_string(),
                ))),
            ),
            (
                "42",
                Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Integer(42))),
            ),
            (
                "(true)",
                Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        true,
                    ))),
                ))),
            ),
            (
                "(false)",
                Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        false,
                    ))),
                ))),
            ),
            (
                r#"("var3")"#,
                Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                    Expression::PrimaryExpression(PrimaryExpression::Str("var3".to_string())),
                ))),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(primary_expr().parse(&input), Ok(expected));
        }
    }
    {
        let data = vec!["$var1", "❤", "?", "="];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(expr().parse(&input).is_err());
        }
    }
}

#[test]
fn test_postfix_expr() {
    {
        let data = vec![
            (
                "foo()",
                Expression::FunctionCall(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("foo".to_string())),
                    )),
                    vec![],
                ),
            ),
            (
                "foo(1)",
                Expression::FunctionCall(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("foo".to_string())),
                    )),
                    vec![Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))],
                ),
            ),
            (
                r#"func123("string")"#,
                Expression::FunctionCall(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("func123".to_string())),
                    )),
                    vec![Expression::PrimaryExpression(PrimaryExpression::Str(
                        "string".to_string(),
                    ))],
                ),
            ),
            (
                r#"func123("string", 342)"#,
                Expression::FunctionCall(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("func123".to_string())),
                    )),
                    vec![
                        Expression::PrimaryExpression(PrimaryExpression::Str("string".to_string())),
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(342),
                        )),
                    ],
                ),
            ),
            (
                r#"func123("string", 342, x + y)"#,
                Expression::FunctionCall(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("func123".to_string())),
                    )),
                    vec![
                        Expression::PrimaryExpression(PrimaryExpression::Str("string".to_string())),
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(342),
                        )),
                        Expression::BinaryExpression(BinaryExpression::Plus(
                            Box::new(Expression::PrimaryExpression(
                                PrimaryExpression::Identifier(Identifier("x".to_string())),
                            )),
                            Box::new(Expression::PrimaryExpression(
                                PrimaryExpression::Identifier(Identifier("y".to_string())),
                            )),
                        )),
                    ],
                ),
            ),
            (
                "foo[3]",
                Expression::ArrayIndex(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("foo".to_string())),
                    )),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                ),
            ),
            (
                "foo[3 + x]",
                Expression::ArrayIndex(
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("foo".to_string())),
                    )),
                    Box::new(Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(3),
                        ))),
                        Box::new(Expression::PrimaryExpression(
                            PrimaryExpression::Identifier(Identifier("x".to_string())),
                        )),
                    ))),
                ),
            ),
            (
                "foo.y.z",
                Expression::FieldAccess(
                    Box::new(Expression::FieldAccess(
                        Box::new(Expression::PrimaryExpression(
                            PrimaryExpression::Identifier(Identifier("foo".to_string())),
                        )),
                        Box::new(Expression::PrimaryExpression(
                            PrimaryExpression::Identifier(Identifier("y".to_string())),
                        )),
                    )),
                    Box::new(Expression::PrimaryExpression(
                        PrimaryExpression::Identifier(Identifier("z".to_string())),
                    )),
                ),
            ),
            (
                "foo(y).z[3]",
                Expression::ArrayIndex(
                    Box::new(Expression::FieldAccess(
                        Box::new(Expression::FunctionCall(
                            Box::new(Expression::PrimaryExpression(
                                PrimaryExpression::Identifier(Identifier("foo".to_string())),
                            )),
                            vec![Expression::PrimaryExpression(
                                PrimaryExpression::Identifier(Identifier("y".to_string())),
                            )],
                        )),
                        Box::new(Expression::PrimaryExpression(
                            PrimaryExpression::Identifier(Identifier("z".to_string())),
                        )),
                    )),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                ),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(expr().parse(&input), Ok(expected));
        }
    }
}

#[test]
fn test_arith_expr() {
    {
        let data = vec![
            (
                "1 + 2",
                Expression::BinaryExpression(BinaryExpression::Plus(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(2),
                    ))),
                )),
            ),
            (
                "1 - 2",
                Expression::BinaryExpression(BinaryExpression::Minus(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(2),
                    ))),
                )),
            ),
            (
                "1 + 2 + 3",
                Expression::BinaryExpression(BinaryExpression::Plus(
                    Box::new(Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                )),
            ),
            (
                "1 + 2 - 3",
                Expression::BinaryExpression(BinaryExpression::Minus(
                    Box::new(Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                )),
            ),
            (
                "1 + 2 * 3",
                Expression::BinaryExpression(BinaryExpression::Plus(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::Multiply(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(3),
                        ))),
                    ))),
                )),
            ),
            (
                "1 + 2 * 3 / 4",
                Expression::BinaryExpression(BinaryExpression::Plus(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::Divide(
                        Box::new(Expression::BinaryExpression(BinaryExpression::Multiply(
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(2),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(3),
                            ))),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(4),
                        ))),
                    ))),
                )),
            ),
            (
                "(1 + 2)",
                Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                    Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    )),
                ))),
            ),
            (
                "1 + (2 + 3)",
                Expression::BinaryExpression(BinaryExpression::Plus(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Paren(
                        Box::new(Expression::BinaryExpression(BinaryExpression::Plus(
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(2),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(3),
                            ))),
                        ))),
                    ))),
                )),
            ),
            (
                "1 ^ 2 & 3 | 4",
                Expression::BinaryExpression(BinaryExpression::BitOr(
                    Box::new(Expression::BinaryExpression(BinaryExpression::BitXor(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::BinaryExpression(BinaryExpression::BitAnd(
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(2),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(3),
                            ))),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(4),
                    ))),
                )),
            ),
            (
                "5 % 2 % 1",
                Expression::BinaryExpression(BinaryExpression::Modulo(
                    Box::new(Expression::BinaryExpression(BinaryExpression::Modulo(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(5),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                )),
            ),
            (
                "1 + 2 * 3 / 4 ^ 5 & 6",
                Expression::BinaryExpression(BinaryExpression::BitXor(
                    Box::new(Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::BinaryExpression(BinaryExpression::Divide(
                            Box::new(Expression::BinaryExpression(BinaryExpression::Multiply(
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(2)),
                                )),
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(3)),
                                )),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(4),
                            ))),
                        ))),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::BitAnd(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(5),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(6),
                        ))),
                    ))),
                )),
            ),
            (
                "1 << 2 >> 3",
                Expression::BinaryExpression(BinaryExpression::RightShift(
                    Box::new(Expression::BinaryExpression(BinaryExpression::LeftShift(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                )),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(expr().parse(&input), Ok(expected));
        }
    }
}

#[test]
fn test_logic_expr() {
    {
        let data = vec![
            (
                "1 || 2",
                Expression::BinaryExpression(BinaryExpression::LogicalOr(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(2),
                    ))),
                )),
            ),
            (
                "1 || 2 || 3",
                Expression::BinaryExpression(BinaryExpression::LogicalOr(
                    Box::new(Expression::BinaryExpression(BinaryExpression::LogicalOr(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(3),
                    ))),
                )),
            ),
            (
                "1 || 2 && 3",
                Expression::BinaryExpression(BinaryExpression::LogicalOr(
                    Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                        Constant::Integer(1),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::LogicalAnd(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(3),
                        ))),
                    ))),
                )),
            ),
            (
                "1 == 2 && 3 != 4",
                Expression::BinaryExpression(BinaryExpression::LogicalAnd(
                    Box::new(Expression::BinaryExpression(BinaryExpression::Equals(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::NotEquals(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(3),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(4),
                        ))),
                    ))),
                )),
            ),
            (
                "1 < 2 && 3 <= 4 || 5 > 6 && 7 >= 8",
                Expression::BinaryExpression(BinaryExpression::LogicalOr(
                    Box::new(Expression::BinaryExpression(BinaryExpression::LogicalAnd(
                        Box::new(Expression::BinaryExpression(BinaryExpression::LessThan(
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(1),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(2),
                            ))),
                        ))),
                        Box::new(Expression::BinaryExpression(
                            BinaryExpression::LessThanEquals(
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(3)),
                                )),
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(4)),
                                )),
                            ),
                        )),
                    ))),
                    Box::new(Expression::BinaryExpression(BinaryExpression::LogicalAnd(
                        Box::new(Expression::BinaryExpression(BinaryExpression::GreaterThan(
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(5),
                            ))),
                            Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(6),
                            ))),
                        ))),
                        Box::new(Expression::BinaryExpression(
                            BinaryExpression::GreaterThanEquals(
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(7)),
                                )),
                                Box::new(Expression::PrimaryExpression(
                                    PrimaryExpression::Constant(Constant::Integer(8)),
                                )),
                            ),
                        )),
                    ))),
                )),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(expr().parse(&input), Ok(expected));
        }
    }
}

#[test]
fn test_unary_expr() {
    {
        let data = vec![(
            "~!-5",
            Expression::UnaryExpression(UnaryExpression::BitNot(Box::new(
                Expression::UnaryExpression(UnaryExpression::Not(Box::new(
                    Expression::UnaryExpression(UnaryExpression::Minus(Box::new(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(5),
                        )),
                    ))),
                ))),
            ))),
        )];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(expr().parse(&input), Ok(expected));
        }
    }
    {
        let data = vec!["=2", "/3+4", "$$"];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(expr().parse(&input).is_err());
        }
    }
}

#[test]
fn test_writespace_ignored_expr() {
    {
        let data = vec![
            (" ~ ! -   5", "~!-5"),
            (
                "1<2&&3   <=4        ||  5>6&&7>=8",
                "1 < 2 && 3 <= 4 || 5 > 6 && 7 >= 8",
            ),
            (
                "1<2&&3   <=4        ||  5>6&&7>=8",
                "1 < 2 && 3 <= 4 || 5 > 6 && 7 >= 8",
            ),
            (" 1<<2>>  3", "1 << 2 >> 3"),
            (" func  ( 123   )", "func(123)"),
            ("func  ( 123   ).field [99]", "func(123).field[99]"),
            (
                r#"func123(  "string"  ,   342   , x + y)"#,
                r#"func123("string", 342, x + y)"#,
            ),
            (
                r#"func123("string",342,x+y)"#,
                r#"func123("string", 342, x + y)"#,
            ),
        ];

        for (input, baseline) in data {
            let input: Vec<char> = input.chars().collect();
            let baseline: Vec<char> = baseline.chars().collect();
            assert_eq!(expr().parse(&input), expr().parse(&baseline));
        }
    }
}

#[test]
fn test_block_stmt() {
    {
        let data = vec![
            (
                "for x in y { 1; }",
                Statement::BlockStatement(BlockStatement::For(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "y".to_string(),
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                )),
            ),
            (
                "while true { 1; }",
                Statement::BlockStatement(BlockStatement::While(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        true,
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                )),
            ),
            (
                "while false { break; continue; }",
                Statement::BlockStatement(BlockStatement::While(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        false,
                    ))),
                    vec![
                        Statement::JumpStatement(JumpStatement::Break),
                        Statement::JumpStatement(JumpStatement::Continue),
                    ],
                )),
            ),
            (
                "while (true) { 1; }",
                Statement::BlockStatement(BlockStatement::While(
                    Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Boolean(true),
                        )),
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                )),
            ),
            (
                "if true { 1; }",
                Statement::BlockStatement(BlockStatement::If(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        true,
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                    Vec::new(),
                )),
            ),
            (
                "if (true) { 1; }",
                Statement::BlockStatement(BlockStatement::If(
                    Expression::PrimaryExpression(PrimaryExpression::Paren(Box::new(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Boolean(true),
                        )),
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                    Vec::new(),
                )),
            ),
            (
                "if true { 1; } else { 2; }",
                Statement::BlockStatement(BlockStatement::If(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        true,
                    ))),
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        )),
                    )],
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        )),
                    )],
                )),
            ),
            (
                "if true { if false { 1; } } else { 2; }",
                Statement::BlockStatement(BlockStatement::If(
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Boolean(
                        true,
                    ))),
                    vec![Statement::BlockStatement(BlockStatement::If(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Boolean(false),
                        )),
                        vec![Statement::ExpressionStatement(
                            Expression::PrimaryExpression(PrimaryExpression::Constant(
                                Constant::Integer(1),
                            )),
                        )],
                        Vec::new(),
                    ))],
                    vec![Statement::ExpressionStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        )),
                    )],
                )),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(stmt().parse(&input), Ok(expected));
        }
    }
    {
        let data = vec![
            "while false 1;",
            "while false { 1;",
            "while false  1; }",
            "for (x) in y { 1; }",
            r#"for "str" in y { 1; }"#,
            "for x+y in z { 1; }",
            "for x+y in z 1; }",
            "for x+y z { 1; }",
            "for x in y { 1 }",
            "if true 1; else 2;",
            "if if true { 1; }",
        ];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(stmt().parse(&input).is_err());
        }
    }
}

#[test]
fn test_assign_stmt() {
    {
        let data = vec![
            (
                "x = y;",
                Statement::AssignStatement(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "y".to_string(),
                    ))),
                ),
            ),
            (
                "x = 1 + 2;",
                Statement::AssignStatement(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                    Expression::BinaryExpression(BinaryExpression::Plus(
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(1),
                        ))),
                        Box::new(Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(2),
                        ))),
                    )),
                ),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(stmt().parse(&input), Ok(expected));
        }
    }
    {
        let data = vec!["x = y = z"];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(stmt().parse(&input).is_err());
        }
    }
}

#[test]
fn test_builtin_stmt() {
    {
        let data = vec![
            ("quit;", Statement::BuiltinStatement(BuiltinStatement::Quit)),
            ("help;", Statement::BuiltinStatement(BuiltinStatement::Help)),
            (
                "print x;",
                Statement::BuiltinStatement(BuiltinStatement::Print(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                )),
            ),
            (
                r#"filesystem "/mnt/btrfs";"#,
                Statement::BuiltinStatement(BuiltinStatement::Filesystem(
                    Expression::PrimaryExpression(PrimaryExpression::Str("/mnt/btrfs".to_string())),
                )),
            ),
        ];

        for (input, expected) in data {
            let input: Vec<char> = input.chars().collect();
            assert_eq!(stmt().parse(&input), Ok(expected));
        }
    }
    {
        let data = vec!["filesystem foo;", "filesystem quit;"];

        for input in data {
            let input: Vec<char> = input.chars().collect();
            assert!(stmt().parse(&input).is_err());
        }
    }
}

#[test]
fn test_program() {
    {
        let data = vec![(
            "x = 3; if x { x = 5; } print x;",
            vec![
                Statement::AssignStatement(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                    Expression::PrimaryExpression(PrimaryExpression::Constant(Constant::Integer(
                        3,
                    ))),
                ),
                Statement::BlockStatement(BlockStatement::If(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                    vec![Statement::AssignStatement(
                        Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                            "x".to_string(),
                        ))),
                        Expression::PrimaryExpression(PrimaryExpression::Constant(
                            Constant::Integer(5),
                        )),
                    )],
                    Vec::new(),
                )),
                Statement::BuiltinStatement(BuiltinStatement::Print(
                    Expression::PrimaryExpression(PrimaryExpression::Identifier(Identifier(
                        "x".to_string(),
                    ))),
                )),
            ],
        )];

        for (input, expected) in data {
            assert_eq!(parse(input), Ok(expected));
        }
    }

    // We can only test some things doing a whole-program parse b/c it's
    // hard to tell if the parser hit an error and simply stopped parsing
    // (leaving some input unconsumed).
    {
        let data = vec!["if true { 1; } else else false;", "1 + 2", "quit alas;"];

        for input in data {
            assert!(parse(input).is_err());
        }
    }
}
