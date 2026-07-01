//! Surface syntax front end for the Sprint 05 reduced subset.
//!
//! Lexer/parser code cites `docs/syntax.md`; elaboration targets the verified reduced core.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod pretty;

pub use ast::{Boundedness, Decl, Expr, FnDecl, Program, Span, Spanned, TypeExpr};
pub use lexer::{lex, LexError, Token, TokenKind};
pub use parser::{parse_program, ParseError};
pub use pretty::pretty_program;
