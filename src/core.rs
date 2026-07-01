//! Reduced core AST for Sprint 01.
//!
//! This is an internal/programmatic representation of `docs/calculus.md §3` restricted by
//! `docs/calculus.md §10`. It deliberately does not include a parser or surface syntax.

use std::collections::BTreeSet;
use std::fmt;

use crate::grade::{Bound, Eff, Label, Region};

pub type Name = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Unit,
    Nat,
    Arrow(Box<Type>, Box<Type>),
    Cont(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unit => f.write_str("Unit"),
            Type::Nat => f.write_str("Nat"),
            Type::Arrow(arg, ret) => write!(f, "({arg} -> {ret})"),
            Type::Cont(arg, ret) => write!(f, "Cont[{arg},{ret}]"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContId(pub u64);

impl fmt::Display for ContId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "κ{}", self.0)
    }
}

/// Core term grammar (`calculus.md §3.2`) restricted to Sprint 01 (`§10`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(Name),
    Unit,
    Nat(u64),
    Lam {
        param: Name,
        param_ty: Type,
        body: Box<Term>,
    },
    App(Box<Term>, Box<Term>),
    Let {
        var: Name,
        expr: Box<Term>,
        body: Box<Term>,
    },
    Fix {
        func: Name,
        param: Name,
        param_ty: Type,
        body: Box<Term>,
        tag: RecursionTag,
    },
    Perform(Label, Box<Term>),
    Handle {
        body: Box<Term>,
        handler: Handler,
    },
    Resume {
        kont: Box<Term>,
        arg: Box<Term>,
    },
    /// Runtime-only one-shot continuation value introduced by `H-op` (`calculus.md §5`).
    Cont(ContId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Handler {
    pub return_var: Name,
    pub return_body: Box<Term>,
    pub op_label: Label,
    pub op_param: Name,
    pub op_k: Name,
    pub op_body: Box<Term>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RecursionTag {
    Structural,
    Measure,
    Div,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Divergence {
    Terminates,
    Div,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CoverageTag {
    LambdaApp,
    Let,
    FixStructural,
    FixMeasure,
    Perform,
    HandleResuming,
    HandleDropped,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContinuationUseFacts {
    pub introduced: u32,
    pub resumed: u32,
    pub dropped: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    pub ty: Type,
    pub effects: Eff,
    pub bound: Bound,
    pub region: Region,
    pub continuation_uses: ContinuationUseFacts,
    pub divergence: Divergence,
    pub coverage: BTreeSet<CoverageTag>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedTerm {
    pub term: Term,
    pub witness: Witness,
    pub name: &'static str,
}

impl Term {
    #[must_use]
    pub fn var(name: impl Into<Name>) -> Self {
        Self::Var(name.into())
    }

    #[must_use]
    pub fn nat(value: u64) -> Self {
        Self::Nat(value)
    }

    #[must_use]
    pub fn unit() -> Self {
        Self::Unit
    }

    #[must_use]
    pub fn is_value(&self) -> bool {
        matches!(
            self,
            Self::Unit | Self::Nat(_) | Self::Lam { .. } | Self::Cont(_)
        )
    }

    /// Capture-avoiding enough for generated terms, which use globally fresh names.
    /// Implements substitution used by β/let/unfold/H-return/H-op (`calculus.md §5`).
    #[must_use]
    pub fn subst(&self, name: &str, replacement: &Self) -> Self {
        match self {
            Self::Var(var) if var == name => replacement.clone(),
            Self::Var(_) | Self::Unit | Self::Nat(_) | Self::Cont(_) => self.clone(),
            Self::Lam {
                param,
                param_ty,
                body,
            } if param == name => Self::Lam {
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: body.clone(),
            },
            Self::Lam {
                param,
                param_ty,
                body,
            } => Self::Lam {
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(body.subst(name, replacement)),
            },
            Self::App(fun, arg) => Self::App(
                Box::new(fun.subst(name, replacement)),
                Box::new(arg.subst(name, replacement)),
            ),
            Self::Let { var, expr, body } if var == name => Self::Let {
                var: var.clone(),
                expr: Box::new(expr.subst(name, replacement)),
                body: body.clone(),
            },
            Self::Let { var, expr, body } => Self::Let {
                var: var.clone(),
                expr: Box::new(expr.subst(name, replacement)),
                body: Box::new(body.subst(name, replacement)),
            },
            Self::Fix {
                func,
                param,
                param_ty,
                body,
                tag,
            } if func == name || param == name => Self::Fix {
                func: func.clone(),
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: body.clone(),
                tag: *tag,
            },
            Self::Fix {
                func,
                param,
                param_ty,
                body,
                tag,
            } => Self::Fix {
                func: func.clone(),
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(body.subst(name, replacement)),
                tag: *tag,
            },
            Self::Perform(label, arg) => {
                Self::Perform(*label, Box::new(arg.subst(name, replacement)))
            }
            Self::Handle { body, handler } => Self::Handle {
                body: Box::new(body.subst(name, replacement)),
                handler: handler.subst(name, replacement),
            },
            Self::Resume { kont, arg } => Self::Resume {
                kont: Box::new(kont.subst(name, replacement)),
                arg: Box::new(arg.subst(name, replacement)),
            },
        }
    }

    /// Normalize runtime continuation IDs so determinism compares structure rather than
    /// fresh allocation numbers.
    #[must_use]
    pub fn normalize_cont_ids(&self) -> Self {
        match self {
            Self::Cont(_) => Self::Cont(ContId(0)),
            Self::Var(_) | Self::Unit | Self::Nat(_) => self.clone(),
            Self::Lam {
                param,
                param_ty,
                body,
            } => Self::Lam {
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(body.normalize_cont_ids()),
            },
            Self::App(fun, arg) => Self::App(
                Box::new(fun.normalize_cont_ids()),
                Box::new(arg.normalize_cont_ids()),
            ),
            Self::Let { var, expr, body } => Self::Let {
                var: var.clone(),
                expr: Box::new(expr.normalize_cont_ids()),
                body: Box::new(body.normalize_cont_ids()),
            },
            Self::Fix {
                func,
                param,
                param_ty,
                body,
                tag,
            } => Self::Fix {
                func: func.clone(),
                param: param.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(body.normalize_cont_ids()),
                tag: *tag,
            },
            Self::Perform(label, arg) => Self::Perform(*label, Box::new(arg.normalize_cont_ids())),
            Self::Handle { body, handler } => Self::Handle {
                body: Box::new(body.normalize_cont_ids()),
                handler: handler.normalize_cont_ids(),
            },
            Self::Resume { kont, arg } => Self::Resume {
                kont: Box::new(kont.normalize_cont_ids()),
                arg: Box::new(arg.normalize_cont_ids()),
            },
        }
    }
}

impl Handler {
    #[must_use]
    pub fn subst(&self, name: &str, replacement: &Term) -> Self {
        let return_body = if self.return_var == name {
            self.return_body.clone()
        } else {
            Box::new(self.return_body.subst(name, replacement))
        };
        let op_body = if self.op_param == name || self.op_k == name {
            self.op_body.clone()
        } else {
            Box::new(self.op_body.subst(name, replacement))
        };
        Self {
            return_var: self.return_var.clone(),
            return_body,
            op_label: self.op_label,
            op_param: self.op_param.clone(),
            op_k: self.op_k.clone(),
            op_body,
        }
    }

    #[must_use]
    pub fn normalize_cont_ids(&self) -> Self {
        Self {
            return_var: self.return_var.clone(),
            return_body: Box::new(self.return_body.normalize_cont_ids()),
            op_label: self.op_label,
            op_param: self.op_param.clone(),
            op_k: self.op_k.clone(),
            op_body: Box::new(self.op_body.normalize_cont_ids()),
        }
    }
}

impl fmt::Display for Handler {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{ return {} -> {}; {} {} {} -> {} }}",
            self.return_var,
            self.return_body,
            self.op_label,
            self.op_param,
            self.op_k,
            self.op_body
        )
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => f.write_str(name),
            Term::Unit => f.write_str("()"),
            Term::Nat(value) => write!(f, "{value}"),
            Term::Lam {
                param,
                param_ty,
                body,
            } => write!(f, "(λ{param}:{param_ty}. {body})"),
            Term::App(fun, arg) => write!(f, "({fun} {arg})"),
            Term::Let { var, expr, body } => write!(f, "(let {var} = {expr} in {body})"),
            Term::Fix {
                func,
                param,
                param_ty,
                body,
                tag,
            } => write!(f, "(fix[{tag:?}] {func}. λ{param}:{param_ty}. {body})"),
            Term::Perform(label, arg) => write!(f, "(perform {label} {arg})"),
            Term::Handle { body, handler } => write!(f, "(handle {body} with {handler})"),
            Term::Resume { kont, arg } => write!(f, "(resume {kont} {arg})"),
            Term::Cont(id) => write!(f, "{id}"),
        }
    }
}
