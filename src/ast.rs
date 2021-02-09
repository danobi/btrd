#[derive(Debug, PartialEq)]
pub enum UnaryExpression {
    /// `~`
    BitNot(Box<Expression>),
    /// `!`
    Not(Box<Expression>),
    /// `-`
    Minus(Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub enum BinaryExpression {
    /// `+`
    Plus(Box<Expression>, Box<Expression>),
    /// `-`
    Minus(Box<Expression>, Box<Expression>),
    /// `*`
    Multiply(Box<Expression>, Box<Expression>),
    /// `/`
    Divide(Box<Expression>, Box<Expression>),
    /// `%`
    Modulo(Box<Expression>, Box<Expression>),
    /// `==`
    Equals(Box<Expression>, Box<Expression>),
    /// `!=`
    NotEquals(Box<Expression>, Box<Expression>),
    /// `&&`
    LogicalAnd(Box<Expression>, Box<Expression>),
    /// `||`
    LogicalOr(Box<Expression>, Box<Expression>),
    /// `|`
    BitOr(Box<Expression>, Box<Expression>),
    /// `&`
    BitAnd(Box<Expression>, Box<Expression>),
    /// `^`
    BitXor(Box<Expression>, Box<Expression>),
    /// `<<`
    LeftShift(Box<Expression>, Box<Expression>),
    /// `>>`
    RightShift(Box<Expression>, Box<Expression>),
    // `<`
    LessThan(Box<Expression>, Box<Expression>),
    // `<=`
    LessThanEquals(Box<Expression>, Box<Expression>),
    // `>`
    GreaterThan(Box<Expression>, Box<Expression>),
    // `>=`
    GreaterThanEquals(Box<Expression>, Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub enum Constant {
    Integer(i64),
    Boolean(bool),
}

#[derive(Debug, PartialEq)]
pub struct Identifier(pub String);

#[derive(Debug, PartialEq)]
pub enum PrimaryExpression {
    Identifier(Identifier),
    Constant(Constant),
    Str(String),
    Paren(Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    PrimaryExpression(PrimaryExpression),
    /// (expression, field)
    FieldAccess(Box<Expression>, Box<Expression>),
    /// (expression, index)
    ArrayIndex(Box<Expression>, Box<Expression>),
    /// (function, arguments)
    FunctionCall(Box<Expression>, Vec<Expression>),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
}

#[derive(Debug, PartialEq)]
pub enum BlockStatement {
    /// (condition, true_body, false_body)
    If(Expression, Vec<Statement>, Vec<Statement>),
    /// (condition, stmts)
    While(Expression, Vec<Statement>),
    /// (ident, range, body)
    For(Expression, Expression, Vec<Statement>),
}

#[derive(Debug, PartialEq)]
pub enum JumpStatement {
    Break,
    Continue,
}

#[derive(Debug, PartialEq)]
pub enum BuiltinStatement {
    Help,
    Quit,
    Filesystem(Expression),
    Print(Expression),
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    AssignStatement(Expression, Expression),
    BlockStatement(BlockStatement),
    JumpStatement(JumpStatement),
    BuiltinStatement(BuiltinStatement),
    ExpressionStatement(Expression),
}
