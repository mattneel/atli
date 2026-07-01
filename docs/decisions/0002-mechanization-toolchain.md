# ADR 0002: Mechanization toolchain

## Status

Accepted — 2026-07-01.

## Decision

Use plain Rocq/Coq for the Sprint 04 mechanization scaffold, without Iris yet.

The checked-in proof files are kept compatible with Coq/Rocq compatibility binaries and
standard library only. CI pins the Ubuntu Noble package version `coq=8.18.0+dfsg-1build2`
(`coqc --version`: Coq 8.18.0, OCaml 4.14.1). Local verification in this sprint used the
same package.

## Rationale

`docs/calculus.md §10` names Rocq/Iris as the long-term mechanization target. Iris is the
right eventual tool for one-shot continuation/resource arguments, but Sprint 04's required
`Qed` obligations are finite grade laws, syntactic substitution infrastructure, the
handler mention/resume lemma, and step determinism. Plain Rocq is enough for those while
keeping setup cost low and CI fast. The development is split so an Iris dependency can be
introduced later around the one-shot soundness rung without rewriting the syntax, typing,
or step definitions.

## Binder representation

Use named binders with decidable string equality for this scaffold. This mirrors the Rust
AST and makes the golden-term bridge legible. Substitution lemmas are therefore stated for
the non-handler fragment with the usual shadowing side conditions. If later preservation
work becomes substitution-heavy, a de Bruijn or locally nameless refactor remains an
explicit mechanization choice rather than an implicit fork from the Rust core.
