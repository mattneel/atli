# Elaboration mapping

The surface-to-core mapping is specified in [`docs/elaboration.md`](../../docs/elaboration.md). Important mappings include decimal `Nat` to unary core constructors, arithmetic operators to injected prelude recursion, top-level SCCs to `fix*`, and handlers to the amended core handler rule.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.
