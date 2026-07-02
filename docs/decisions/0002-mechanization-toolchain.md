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

## Sprint 15 amendment — binder and latent-arrow decisions

Preservation work kept named binders rather than refactoring to de Bruijn. The current
scaffold's substitution surface remains small enough for the Sprint 15 obligations, while
bridge legibility stays valuable.

Finding nineteen corrected the mechanized type representation: arrows now carry the
latent effect and boundedness row from `docs/calculus.md §3.1/§4.2/§4.3` as
`TyArrow a ε β b`. This is a fidelity correction, not a new calculus feature; erasing the
latent row made the Rocq model launder effects and `β` through higher-order calls even
though the paper and Rust checker already accounted for them.

Sprint 16 note: the de Bruijn question is dissolved -- `subst` is shadow-aware,
empty-context preservation substitutes only closed values (which cannot be captured), so
the closed-value substitution lemma is provable over named binders as they stand; no
representation refactor.
