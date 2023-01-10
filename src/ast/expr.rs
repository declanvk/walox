use smol_str::SmolStr;

use crate::{
    ast::visit::{Visitable, Visitor},
    scanner::{Literal, TokenType},
    span::Span,
};
use std::{convert::TryFrom, fmt, sync::Arc};

/// Errors that occur when converting to AST elements
#[derive(Debug, thiserror::Error, Clone, PartialEq)]
pub enum ConversionError {
    /// An error that occurs when converting from a raw `TokenType` to a
    /// specific `{Binary,Unary}OpKind`
    #[error("[{:?}] does not correspond to any operation.", .0)]
    Op(TokenType),

    /// An error that occurs when mapping token literals to expression literals
    #[error("the literal [{:?}] has no equivalent expression.", .0)]
    Literal(Literal),
}

/// Syntax tree of a lox expression
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    /// The type of expression
    pub kind: ExprKind,
    /// The continuous block of code this expression covers
    pub span: Span,
}

impl Visitable for Expr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let Expr { kind, .. } = self;

        match kind {
            ExprKind::Binary(e) => e.visit_with(visitor),
            ExprKind::Grouping(e) => e.visit_with(visitor),
            ExprKind::Literal(e) => e.visit_with(visitor),
            ExprKind::Unary(e) => e.visit_with(visitor),
            ExprKind::Var(e) => e.visit_with(visitor),
            ExprKind::Assign(e) => e.visit_with(visitor),
            ExprKind::Logical(e) => e.visit_with(visitor),
            ExprKind::Call(e) => e.visit_with(visitor),
            ExprKind::Get(e) => e.visit_with(visitor),
            ExprKind::Set(e) => e.visit_with(visitor),
            ExprKind::This(e) => e.visit_with(visitor),
            ExprKind::Super(e) => e.visit_with(visitor),
        }
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_expr(self)
    }
}

/// Different types of expressions
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// A binary operation
    Binary(BinaryExpr),
    /// Different types of binary operations
    Grouping(GroupingExpr),
    /// A literal value
    Literal(LiteralExpr),
    /// A unary operation
    Unary(UnaryExpr),
    /// A logical operation
    Logical(LogicalExpr),
    /// A variable reference
    Var(VarExpr),
    /// An assignment to an existing variable
    Assign(AssignExpr),
    /// An expression that calls a function with the supplied arguments
    Call(CallExpr),
    /// An expression that access a named property on an object
    Get(GetExpr),
    /// An expression that sets the value of a named property on an object
    Set(SetExpr),
    /// An expression that references the value of the instance that was the
    /// original owner of the method containing `this`.
    This(ThisExpr),
    /// An expression that acts as a property access on the superclass
    Super(SuperExpr),
}

impl From<BinaryExpr> for ExprKind {
    fn from(v: BinaryExpr) -> Self {
        ExprKind::Binary(v)
    }
}

impl From<UnaryExpr> for ExprKind {
    fn from(v: UnaryExpr) -> Self {
        ExprKind::Unary(v)
    }
}

impl From<LogicalExpr> for ExprKind {
    fn from(v: LogicalExpr) -> Self {
        ExprKind::Logical(v)
    }
}

impl From<LiteralExpr> for ExprKind {
    fn from(v: LiteralExpr) -> Self {
        ExprKind::Literal(v)
    }
}

impl From<GroupingExpr> for ExprKind {
    fn from(v: GroupingExpr) -> Self {
        ExprKind::Grouping(v)
    }
}

impl From<VarExpr> for ExprKind {
    fn from(v: VarExpr) -> Self {
        ExprKind::Var(v)
    }
}

impl From<AssignExpr> for ExprKind {
    fn from(v: AssignExpr) -> Self {
        ExprKind::Assign(v)
    }
}

impl From<CallExpr> for ExprKind {
    fn from(v: CallExpr) -> Self {
        ExprKind::Call(v)
    }
}

impl From<GetExpr> for ExprKind {
    fn from(v: GetExpr) -> Self {
        ExprKind::Get(v)
    }
}

impl From<SetExpr> for ExprKind {
    fn from(v: SetExpr) -> Self {
        ExprKind::Set(v)
    }
}

impl From<ThisExpr> for ExprKind {
    fn from(v: ThisExpr) -> Self {
        ExprKind::This(v)
    }
}

impl From<SuperExpr> for ExprKind {
    fn from(v: SuperExpr) -> Self {
        ExprKind::Super(v)
    }
}

/// A binary operation
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    /// The first argument to the operation
    pub left: Arc<Expr>,
    /// The type of binary operation
    pub operator: BinaryOpKind,
    /// The second argument to the operation
    pub right: Arc<Expr>,
}

impl Visitable for BinaryExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let BinaryExpr { left, right, .. } = self;

        let o1 = left.visit_with(visitor);
        let o2 = right.visit_with(visitor);

        visitor.combine_output(o1, o2)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_binary_expr(self)
    }
}

/// Different types of binary operations
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum BinaryOpKind {
    /// Multiplication operation, symbolized by `*`
    Mult,
    /// Addition operation, symbolized by `+`
    Add,
    /// Subtraction operation, symbolized by `-`
    Sub,
    /// Division operation, symbolized by `/`
    Div,

    /// Boolean AND operation, symbolized by `and`
    And,
    /// Boolean OR operation, symbolized by `or`
    Or,

    /// Comparison equal operation, symbolized by `==`
    Equal,
    /// Comparison not equal operation, symbolized by `!=`
    NotEqual,
    /// Comparison greater than operation, symbolized by `>`
    Greater,
    /// Comparison less than operation, symbolized by `<`
    Less,
    /// Comparison greater than or equal operation, symbolized by `>=`
    GreaterEqual,
    /// Comparison less than or equal operation, symbolized by `<=`
    LessEqual,
}

impl BinaryOpKind {
    /// Return a static string which symbolizes this operation
    pub fn symbol(&self) -> &'static str {
        match self {
            BinaryOpKind::Mult => "*",
            BinaryOpKind::Add => "+",
            BinaryOpKind::Sub => "-",
            BinaryOpKind::Div => "/",
            BinaryOpKind::And => "and",
            BinaryOpKind::Or => "or",
            BinaryOpKind::Equal => "==",
            BinaryOpKind::NotEqual => "!=",
            BinaryOpKind::Greater => ">",
            BinaryOpKind::Less => "<",
            BinaryOpKind::GreaterEqual => ">=",
            BinaryOpKind::LessEqual => "<=",
        }
    }
}

impl TryFrom<TokenType> for BinaryOpKind {
    type Error = ConversionError;

    fn try_from(value: TokenType) -> Result<Self, Self::Error> {
        match value {
            // TokenType::Dot => {}
            TokenType::Minus => Ok(BinaryOpKind::Sub),
            TokenType::Plus => Ok(BinaryOpKind::Add),
            TokenType::Slash => Ok(BinaryOpKind::Div),
            TokenType::Star => Ok(BinaryOpKind::Mult),

            TokenType::BangEqual => Ok(BinaryOpKind::NotEqual),
            TokenType::EqualEqual => Ok(BinaryOpKind::Equal),
            TokenType::Greater => Ok(BinaryOpKind::Greater),
            TokenType::GreaterEqual => Ok(BinaryOpKind::GreaterEqual),
            TokenType::Less => Ok(BinaryOpKind::Less),
            TokenType::LessEqual => Ok(BinaryOpKind::LessEqual),

            TokenType::And => Ok(BinaryOpKind::And),
            TokenType::Or => Ok(BinaryOpKind::Or),

            t => Err(ConversionError::Op(t)),
        }
    }
}

impl fmt::Display for BinaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

/// An expression that is delimited by parentheses
#[derive(Debug, Clone, PartialEq)]
pub struct GroupingExpr {
    /// The inner expression
    pub inner: Arc<Expr>,
}

impl Visitable for GroupingExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let GroupingExpr { inner, .. } = self;

        inner.visit_with(visitor)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_grouping_expr(self)
    }
}

/// A literal value
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    /// A boolean value
    Boolean(bool),
    /// A numeric value
    Number(f64),
    /// A string value (UTF-8)
    String(SmolStr),
    /// A null value
    Null,
}

impl fmt::Display for LiteralExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralExpr::Boolean(b) => write!(f, "{b}"),
            LiteralExpr::Number(n) => write!(f, "{n}"),
            LiteralExpr::String(s) => write!(f, "\"{s}\""),
            LiteralExpr::Null => write!(f, "nil"),
        }
    }
}

impl TryFrom<Literal> for LiteralExpr {
    type Error = ConversionError;

    fn try_from(value: Literal) -> Result<Self, Self::Error> {
        match value {
            Literal::Number(f) => Ok(LiteralExpr::Number(f)),
            Literal::String(s) => Ok(LiteralExpr::String(s)),
            Literal::Identifier(_) => Err(ConversionError::Literal(value)),
        }
    }
}

impl Visitable for LiteralExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_literal_expr(self)
    }
}

/// A unary operation
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    /// The type of unary operation
    pub operator: UnaryOpKind,
    /// The argument to the operation
    pub right: Arc<Expr>,
}

impl Visitable for UnaryExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let UnaryExpr { right, .. } = self;

        right.visit_with(visitor)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_unary_expr(self)
    }
}

/// Different types of unary operations
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum UnaryOpKind {
    /// Negation operation, symbolized by `-`
    Negate,
    /// Boolean not operation, symbolized by `!`,
    Not,
}

impl UnaryOpKind {
    /// Return a static string which symbolizes this operation
    pub fn symbol(&self) -> &'static str {
        match self {
            UnaryOpKind::Negate => "-",
            UnaryOpKind::Not => "!",
        }
    }
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            UnaryOpKind::Negate => "-",
            UnaryOpKind::Not => "!",
        };

        write!(f, "{s}")
    }
}

impl TryFrom<TokenType> for UnaryOpKind {
    type Error = ConversionError;

    fn try_from(value: TokenType) -> Result<Self, Self::Error> {
        match value {
            TokenType::Minus => Ok(UnaryOpKind::Negate),
            TokenType::Bang => Ok(UnaryOpKind::Not),

            t => Err(ConversionError::Op(t)),
        }
    }
}

/// A logical operation
#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    /// The left operand of the operation
    pub left: Arc<Expr>,
    /// The type of logical operation
    pub operator: LogicalOpKind,
    /// The right operand of the operation
    pub right: Arc<Expr>,
}

impl Visitable for LogicalExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let LogicalExpr { left, right, .. } = self;

        let o1 = left.visit_with(visitor);
        let o2 = right.visit_with(visitor);

        visitor.combine_output(o1, o2)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_logical_expr(self)
    }
}

/// Different types of logical operations
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum LogicalOpKind {
    /// Logical AND operation, if the left and right operands are both true then
    /// the entire expression is true. Else, the expression is false
    And,
    /// Logical OR operation, if the left or right operands is true, then
    /// the entire expression is true. Else, the expression is false
    Or,
}

impl LogicalOpKind {
    /// Return a static string which symbolizes this operation
    pub fn symbol(&self) -> &'static str {
        match self {
            LogicalOpKind::And => "and",
            LogicalOpKind::Or => "or",
        }
    }
}

impl fmt::Display for LogicalOpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

impl TryFrom<TokenType> for LogicalOpKind {
    type Error = ConversionError;

    fn try_from(value: TokenType) -> Result<Self, Self::Error> {
        match value {
            TokenType::And => Ok(LogicalOpKind::And),
            TokenType::Or => Ok(LogicalOpKind::Or),

            t => Err(ConversionError::Op(t)),
        }
    }
}

/// A variable reference expression
#[derive(Debug, Clone, PartialEq)]
pub struct VarExpr {
    /// The name of the variable
    pub name: SmolStr,
}

impl Visitable for VarExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_var_expr(self)
    }
}

/// An assignment to an existing variable
#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    /// The name of the variable
    pub name: SmolStr,
    /// The value of the assignment
    pub value: Arc<Expr>,
}

impl Visitable for AssignExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let AssignExpr { value, .. } = self;

        value.visit_with(visitor)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_assign_expr(self)
    }
}

/// An expression that calls a function with the supplied arguments
#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    /// An expression that should evaluate to a function to call
    pub callee: Arc<Expr>,
    /// The expressions that will be passed to the body of the function called
    pub arguments: Vec<Arc<Expr>>,
}

impl Visitable for CallExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let CallExpr { callee, arguments } = self;

        let o1 = callee.visit_with(visitor);
        let o_args = arguments.visit_with(visitor);

        visitor.combine_output(o1, o_args)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_call_expr(self)
    }
}

/// An expression that access a named property on an object
#[derive(Debug, Clone, PartialEq)]
pub struct GetExpr {
    /// An expression that evaluates to the object that will be accessed
    pub object: Arc<Expr>,
    /// The property name to access
    pub property: SmolStr,
}

impl Visitable for GetExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let GetExpr { object, .. } = self;

        object.visit_with(visitor)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_get_expr(self)
    }
}

/// An expression that sets the value of a named property on an object
#[derive(Debug, Clone, PartialEq)]
pub struct SetExpr {
    /// An expression that evaluates to the object that will be set
    pub object: Arc<Expr>,
    /// The name of the property
    pub property: SmolStr,
    /// The value to set the property to
    pub value: Arc<Expr>,
}

impl Visitable for SetExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        let SetExpr { object, value, .. } = self;

        let o1 = object.visit_with(visitor);
        let o2 = value.visit_with(visitor);

        visitor.combine_output(o1, o2)
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_set_expr(self)
    }
}

// TODO: rewrite this doc
/// An expression that references the value of the instance that was the
/// original owner of the method containing `this`.
#[derive(Debug, Clone, PartialEq)]
pub struct ThisExpr;

impl ThisExpr {
    /// The string value of the `this` variable.
    pub const VARIABLE_NAME: &'static str = "this";
}

impl Visitable for ThisExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_this_expr(self)
    }
}

/// An expression that acts as a property access on the superclass
#[derive(Debug, Clone, PartialEq)]
pub struct SuperExpr {
    /// The property that is being looked up on the superclass
    pub method: SmolStr,
}

impl Visitable for SuperExpr {
    fn super_visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.default_output()
    }

    fn visit_with<V: Visitor>(&self, visitor: &mut V) -> V::Output {
        visitor.visit_super_expr(self)
    }
}
