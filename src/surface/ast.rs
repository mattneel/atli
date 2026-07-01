use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        Self {
            start: self.start,
            end: other.end,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    #[must_use]
    pub const fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }
}

pub type Name = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Fn(FnDecl),
    Effect(EffectDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnDecl {
    pub public: bool,
    pub name: Spanned<Name>,
    pub params: Vec<Param>,
    pub ret: TypeExpr,
    pub effects: Option<Span>,
    pub boundedness: Boundedness,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: Spanned<Name>,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectDecl {
    pub name: Spanned<Name>,
    pub op: Spanned<Name>,
    pub param: Param,
    pub ret: TypeExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Boundedness {
    Structural,
    Measure(Expr),
    Div(Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    Unit(Span),
    Nat(Span),
    Arrow(Box<TypeExpr>, Box<TypeExpr>, Span),
}

impl TypeExpr {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Unit(span) | Self::Nat(span) | Self::Arrow(_, _, span) => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    #[must_use]
    pub const fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Unit,
    Nat(u64),
    Var(Name),
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    QualifiedCall {
        effect: Name,
        op: Name,
        args: Vec<Expr>,
    },
    Pipe {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Block {
        bindings: Vec<Binding>,
        result: Box<Expr>,
    },
    CaseNat {
        scrutinee: Box<Expr>,
        arms: Vec<CaseArm>,
    },
    Handle {
        body: Box<Expr>,
        clauses: Vec<HandleClause>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub name: Spanned<Name>,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaseArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Zero(Span),
    Bind(Spanned<Name>),
    Wildcard(Span),
}

impl Pattern {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Zero(span) | Self::Wildcard(span) => *span,
            Self::Bind(name) => name.span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandleClause {
    Return {
        var: Spanned<Name>,
        body: Expr,
        span: Span,
    },
    Operation {
        effect: Spanned<Name>,
        op: Spanned<Name>,
        param: Pattern,
        kont: Pattern,
        body: Expr,
        span: Span,
    },
}

impl fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit(_) => f.write_str("Unit"),
            Self::Nat(_) => f.write_str("Nat"),
            Self::Arrow(a, b, _) => write!(f, "{a} -> {b}"),
        }
    }
}
