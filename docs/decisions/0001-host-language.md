# ADR 0001: Host language for the Atli compiler spike

## Status

Accepted for Sprint 01.

## Decision

Use **Rust** for the Atli compiler spike and the Sprint 01 executable core calculus.

## Rationale

The Sprint 01 brief requires an executable reference interpreter, a well-typed-term
generator, property testing with shrinking, and a path toward later MLIR lowering. Rust is
the lowest-friction fit because it provides:

- algebraic data types and exhaustive `match` for representing `λ_Atli` syntax and
  reduction outcomes;
- mature property testing with shrinking through `proptest`;
- a plausible later MLIR path through Rust bindings such as `melior`;
- explicit error handling and predictable systems-level performance.

Zig remains a defensible future target for self-hosting/dogfooding, but choosing it now
would require building more test and MLIR infrastructure before the calculus oracle can
exist. Elixir and TypeScript are intentionally not selected for this compiler core.

## Consequences

- The Sprint 01 scaffold is a Cargo crate.
- Reproducible local commands are exposed through `Justfile` recipes that wrap Cargo.
- This decision does not implement parser, type checker, MLIR lowering, or surface syntax.
