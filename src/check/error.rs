use std::fmt;

use crate::core::{Term, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeErrorKind {
    UnboundVariable(String),
    TypeMismatch { expected: Type, found: Type },
    ExpectedFunction(Type),
    ExpectedContinuation(Type),
    HandlerContinuationUsage(String),
    NonStrictStructuralRecursion,
    Solver(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeError {
    pub rule: &'static str,
    pub section: &'static str,
    pub term: Box<str>,
    pub message: Box<str>,
    pub kind: Box<TypeErrorKind>,
}

impl TypeError {
    #[must_use]
    pub fn new(
        rule: &'static str,
        section: &'static str,
        term: &Term,
        message: impl Into<String>,
        kind: TypeErrorKind,
    ) -> Self {
        Self {
            rule,
            section,
            term: term.to_string().into_boxed_str(),
            message: message.into().into_boxed_str(),
            kind: Box::new(kind),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} rejected `{}`: {}",
            self.rule, self.section, self.term, self.message
        )
    }
}

impl std::error::Error for TypeError {}
