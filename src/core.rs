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
    Array,
    Arrow(Box<Type>, Box<Type>),
    Cont(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unit => f.write_str("Unit"),
            Type::Nat => f.write_str("Nat"),
            Type::Array => f.write_str("Array"),
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
    Zero,
    Succ(Box<Term>),
    /// Runtime array value for `docs/calculus.md §3.2/§5` array reductions.
    Array(Vec<Term>),
    MkArray(Box<Term>, Box<Term>),
    ArrayGet(Box<Term>, Box<Term>),
    ArraySet(Box<Term>, Box<Term>, Box<Term>),
    ArrayLen(Box<Term>),
    Move(Box<Term>),
    Inplace(Box<Term>),
    Freeze(Box<Term>),
    /// Coverage-only origin marker. Surface records/variants lower to arrays in tier 1; this
    /// marker preserves the aggregate origin so generator/checker coverage remains falsifiable
    /// instead of firing for plain array operations.
    Mark(CoverageTag, Box<Term>),
    CaseNat {
        scrutinee: Box<Term>,
        zero_body: Box<Term>,
        succ_var: Name,
        succ_body: Box<Term>,
    },
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
    /// Binding group form `fix*` from `docs/calculus.md §3/§4.8/§7.1`.
    FixGroup {
        bindings: Vec<FixBinding>,
        entry: Name,
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
    pub clauses: Vec<OpClause>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpClause {
    pub op_label: Label,
    pub op_param: Name,
    pub op_k: Name,
    pub op_body: Box<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixBinding {
    pub func: Name,
    pub param: Name,
    pub param_ty: Type,
    pub body: Box<Term>,
    pub tag: RecursionTag,
}

impl Handler {
    #[must_use]
    pub fn single(return_var: Name, return_body: Box<Term>, clause: OpClause) -> Self {
        Self {
            return_var,
            return_body,
            clauses: vec![clause],
        }
    }

    #[must_use]
    pub fn clause_for(&self, label: Label) -> Option<&OpClause> {
        self.clauses.iter().find(|clause| clause.op_label == label)
    }
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
    Array,
    RecordAggregate,
    VariantAggregate,
    DestructureConsume,
    RecordFunctionalUpdate,
    RecordInplaceUpdate,
    ConstructorPatternDescent,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedOutcome {
    Safe,
    UnhandledOperation,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GenerationFacts {
    pub depth: usize,
    pub nested_handlers: bool,
    pub strict_rec_calls: usize,
    pub non_strict_rec_calls: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedTerm {
    pub term: Term,
    pub witness: Witness,
    pub name: &'static str,
    pub expected: ExpectedOutcome,
    pub facts: GenerationFacts,
}

impl Term {
    #[must_use]
    pub fn var(name: impl Into<Name>) -> Self {
        Self::Var(name.into())
    }

    #[must_use]
    pub fn zero() -> Self {
        Self::Zero
    }

    #[must_use]
    pub fn succ(inner: Self) -> Self {
        Self::Succ(Box::new(inner))
    }

    #[must_use]
    pub fn nat(value: u64) -> Self {
        let mut term = Self::Zero;
        for _ in 0..value {
            term = Self::succ(term);
        }
        term
    }

    #[must_use]
    pub fn unit() -> Self {
        Self::Unit
    }

    #[must_use]
    pub fn is_value(&self) -> bool {
        match self {
            Self::Unit | Self::Zero | Self::Lam { .. } | Self::Cont(_) | Self::Array(_) => true,
            Self::Succ(inner) | Self::Mark(_, inner) => inner.is_value(),
            Self::Var(_)
            | Self::MkArray(_, _)
            | Self::ArrayGet(_, _)
            | Self::ArraySet(_, _, _)
            | Self::ArrayLen(_)
            | Self::Move(_)
            | Self::Inplace(_)
            | Self::Freeze(_)
            | Self::CaseNat { .. }
            | Self::App(_, _)
            | Self::Let { .. }
            | Self::Fix { .. }
            | Self::FixGroup { .. }
            | Self::Perform(_, _)
            | Self::Handle { .. }
            | Self::Resume { .. } => false,
        }
    }

    /// Capture-avoiding enough for generated terms, which use globally fresh names.
    /// Implements substitution used by β/let/unfold/case/H-return/H-op (`calculus.md §5`).
    #[must_use]
    pub fn subst(&self, name: &str, replacement: &Self) -> Self {
        match self {
            Self::Var(var) if var == name => replacement.clone(),
            Self::Var(_) | Self::Unit | Self::Zero | Self::Cont(_) | Self::Array(_) => self.clone(),
            Self::Succ(inner) => Self::Succ(Box::new(inner.subst(name, replacement))),
            Self::MkArray(len, fill) => Self::MkArray(
                Box::new(len.subst(name, replacement)),
                Box::new(fill.subst(name, replacement)),
            ),
            Self::ArrayGet(array, index) => Self::ArrayGet(
                Box::new(array.subst(name, replacement)),
                Box::new(index.subst(name, replacement)),
            ),
            Self::ArraySet(array, index, value) => Self::ArraySet(
                Box::new(array.subst(name, replacement)),
                Box::new(index.subst(name, replacement)),
                Box::new(value.subst(name, replacement)),
            ),
            Self::ArrayLen(array) => Self::ArrayLen(Box::new(array.subst(name, replacement))),
            Self::Move(inner) => Self::Move(Box::new(inner.subst(name, replacement))),
            Self::Inplace(inner) => Self::Inplace(Box::new(inner.subst(name, replacement))),
            Self::Freeze(inner) => Self::Freeze(Box::new(inner.subst(name, replacement))),
            Self::Mark(tag, inner) => Self::Mark(*tag, Box::new(inner.subst(name, replacement))),
            Self::CaseNat {
                scrutinee,
                zero_body,
                succ_var,
                succ_body,
            } => Self::CaseNat {
                scrutinee: Box::new(scrutinee.subst(name, replacement)),
                zero_body: Box::new(zero_body.subst(name, replacement)),
                succ_var: succ_var.clone(),
                succ_body: if succ_var == name {
                    succ_body.clone()
                } else {
                    Box::new(succ_body.subst(name, replacement))
                },
            },
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
            Self::FixGroup { bindings, entry } => {
                if bindings.iter().any(|binding| binding.func == name) {
                    self.clone()
                } else {
                    Self::FixGroup {
                        bindings: bindings
                            .iter()
                            .map(|binding| binding.subst(name, replacement))
                            .collect(),
                        entry: entry.clone(),
                    }
                }
            }
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
            Self::Var(_) | Self::Unit | Self::Zero | Self::Array(_) => self.clone(),
            Self::Succ(inner) => Self::Succ(Box::new(inner.normalize_cont_ids())),
            Self::MkArray(len, fill) => Self::MkArray(
                Box::new(len.normalize_cont_ids()),
                Box::new(fill.normalize_cont_ids()),
            ),
            Self::ArrayGet(array, index) => Self::ArrayGet(
                Box::new(array.normalize_cont_ids()),
                Box::new(index.normalize_cont_ids()),
            ),
            Self::ArraySet(array, index, value) => Self::ArraySet(
                Box::new(array.normalize_cont_ids()),
                Box::new(index.normalize_cont_ids()),
                Box::new(value.normalize_cont_ids()),
            ),
            Self::ArrayLen(array) => Self::ArrayLen(Box::new(array.normalize_cont_ids())),
            Self::Move(inner) => Self::Move(Box::new(inner.normalize_cont_ids())),
            Self::Inplace(inner) => Self::Inplace(Box::new(inner.normalize_cont_ids())),
            Self::Freeze(inner) => Self::Freeze(Box::new(inner.normalize_cont_ids())),
            Self::Mark(tag, inner) => Self::Mark(*tag, Box::new(inner.normalize_cont_ids())),
            Self::CaseNat {
                scrutinee,
                zero_body,
                succ_var,
                succ_body,
            } => Self::CaseNat {
                scrutinee: Box::new(scrutinee.normalize_cont_ids()),
                zero_body: Box::new(zero_body.normalize_cont_ids()),
                succ_var: succ_var.clone(),
                succ_body: Box::new(succ_body.normalize_cont_ids()),
            },
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
            Self::FixGroup { bindings, entry } => Self::FixGroup {
                bindings: bindings
                    .iter()
                    .map(FixBinding::normalize_cont_ids)
                    .collect(),
                entry: entry.clone(),
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

impl FixBinding {
    #[must_use]
    pub fn subst(&self, name: &str, replacement: &Term) -> Self {
        let body = if self.func == name || self.param == name {
            self.body.clone()
        } else {
            Box::new(self.body.subst(name, replacement))
        };
        Self {
            func: self.func.clone(),
            param: self.param.clone(),
            param_ty: self.param_ty.clone(),
            body,
            tag: self.tag,
        }
    }

    #[must_use]
    pub fn normalize_cont_ids(&self) -> Self {
        Self {
            func: self.func.clone(),
            param: self.param.clone(),
            param_ty: self.param_ty.clone(),
            body: Box::new(self.body.normalize_cont_ids()),
            tag: self.tag,
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
        let clauses = self
            .clauses
            .iter()
            .map(|clause| clause.subst(name, replacement))
            .collect();
        Self {
            return_var: self.return_var.clone(),
            return_body,
            clauses,
        }
    }

    #[must_use]
    pub fn normalize_cont_ids(&self) -> Self {
        Self {
            return_var: self.return_var.clone(),
            return_body: Box::new(self.return_body.normalize_cont_ids()),
            clauses: self
                .clauses
                .iter()
                .map(OpClause::normalize_cont_ids)
                .collect(),
        }
    }
}

impl OpClause {
    #[must_use]
    pub fn subst(&self, name: &str, replacement: &Term) -> Self {
        let op_body = if self.op_param == name || self.op_k == name {
            self.op_body.clone()
        } else {
            Box::new(self.op_body.subst(name, replacement))
        };
        Self {
            op_label: self.op_label,
            op_param: self.op_param.clone(),
            op_k: self.op_k.clone(),
            op_body,
        }
    }

    #[must_use]
    pub fn normalize_cont_ids(&self) -> Self {
        Self {
            op_label: self.op_label,
            op_param: self.op_param.clone(),
            op_k: self.op_k.clone(),
            op_body: Box::new(self.op_body.normalize_cont_ids()),
        }
    }
}

impl fmt::Display for Handler {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ return {} -> {}", self.return_var, self.return_body)?;
        for clause in &self.clauses {
            write!(
                f,
                "; {} {} {} -> {}",
                clause.op_label, clause.op_param, clause.op_k, clause.op_body
            )?;
        }
        f.write_str(" }")
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => f.write_str(name),
            Term::Unit => f.write_str("()"),
            Term::Zero => f.write_str("zero"),
            Term::Succ(inner) => write!(f, "succ({inner})"),
            Term::Array(values) => write!(f, "array{values:?}"),
            Term::MkArray(len, fill) => write!(f, "mkarray({len}, {fill})"),
            Term::ArrayGet(array, index) => write!(f, "get({array}, {index})"),
            Term::ArraySet(array, index, value) => {
                write!(f, "set({array}, {index}, {value})")
            }
            Term::ArrayLen(array) => write!(f, "len({array})"),
            Term::Move(inner) => write!(f, "move {inner}"),
            Term::Inplace(inner) => write!(f, "inplace {inner}"),
            Term::Freeze(inner) => write!(f, "freeze {inner}"),
            Term::Mark(tag, inner) => write!(f, "mark[{tag:?}]({inner})"),
            Term::CaseNat {
                scrutinee,
                zero_body,
                succ_var,
                succ_body,
            } => write!(
                f,
                "(case {scrutinee} {{ zero => {zero_body}; succ {succ_var} => {succ_body} }})"
            ),
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
            Term::FixGroup { bindings, entry } => {
                write!(f, "(fix* entry {entry} {{")?;
                for binding in bindings {
                    write!(
                        f,
                        " {}[{:?}] = λ{}:{}. {};",
                        binding.func, binding.tag, binding.param, binding.param_ty, binding.body
                    )?;
                }
                f.write_str(" })")
            }
            Term::Perform(label, arg) => write!(f, "(perform {label} {arg})"),
            Term::Handle { body, handler } => write!(f, "(handle {body} with {handler})"),
            Term::Resume { kont, arg } => write!(f, "(resume {kont} {arg})"),
            Term::Cont(id) => write!(f, "{id}"),
        }
    }
}
