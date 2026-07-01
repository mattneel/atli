//! Sprint 01 executable reference for the reduced Atli core calculus.
//!
//! Scope is intentionally limited to `docs/calculus.md §10`: grade algebra, an internal
//! AST, a reference interpreter, a well-typed-by-construction generator, and properties.
//! There is no parser, type checker, MLIR/codegen, or surface-language implementation.

pub mod core;
pub mod gen;
pub mod grade;
pub mod interp;
pub mod props;
