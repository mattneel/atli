//! Executable reference implementation for the reduced Atli core plus the Sprint 05
//! surface front end.
//!
//! The verified back end remains scoped to `docs/calculus.md §10`: grade algebra, core AST,
//! reference interpreter, generator, checker, and properties. The surface parser/elaborator
//! consumes `docs/syntax.md`'s reduced subset and targets that core; there is still no
//! MLIR/codegen now exists for a tier-1 effect-free finite fragment; byte-level frame
//! refinement remains future work.

pub mod check;
pub mod codegen;
pub mod core;
pub mod gen;
pub mod grade;
pub mod interp;
pub mod props;

pub mod diagnostics;
pub mod elaborate;
pub mod surface;
