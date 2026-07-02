# Atli Rocq/Coq mechanization scaffold

Build with:

```sh
make -C proofs
```

Toolchain: Coq/Rocq compatibility binary `coqc` 8.18.0 (OCaml 4.14.1), pinned in CI via
Ubuntu Noble package `coq=8.18.0+dfsg-1build2`. This sprint deliberately uses plain Rocq
without Iris; see `docs/decisions/0002-mechanization-toolchain.md`.

## Proof ladder ledger

| Rung | Theorem family | Status | Owner |
| --- | --- | --- | --- |
| L1 | Grade algebra laws | Qed | Sprint 04 |
| L2 | Substitution and structural lemmas | Qed for current scaffold lemma surface | Sprint 15 |
| L3 | Effectful progress (§8.1) | Qed; effect-closed corollary Qed from L3 | Sprint 16 |
| L4 | Preservation (§8.2) with row/bound order components | Admitted | Future metatheory sprint |
| L5 | Handler mention iff direct resume (§6.2) | Qed | Sprint 04 |
| L6 | One-shot soundness (§8.3) | Stated-Pending-Infrastructure | Future Iris/resource sprint |
| L7 | Boundedness soundness (§8.4), frame-count metric | Admitted with pinned frame-step runway | Future boundedness sprint |
| L8 | Solver/certificate soundness (§7.2/§7.3) | Admitted | Future solver-proof sprint |
| L9 | Uniqueness soundness: `inplace set` and in-place record replacement observationally equal their functional-copy counterparts under affine data usage | Stated-Pending-Infrastructure | Future heap/graded-context sprint |
| L10 | Schedule independence for well-typed task programs (§5/§9.3) | Stated-Pending-Infrastructure | Future concurrent-semantics sprint |
| Coverage | Generics/`^u`, aggregates, tasks, and uniqueness are outside the current mechanized core | Stated-Pending-Infrastructure | Future polymorphic/heap/task Rocq sprint |
| Aux | Step determinism; frame-step erasure | Qed | Sprint 15 |

Current admitted theorem count: 3 (`preservation`, `boundedness_soundness`,
`solver_certificate_soundness`). v0.5.3 supersedes v0.5.2: the prior L3/L4/L8 Qed claims
were previously false because `step` had been degenerated. L6/L9/L10 remain SPI, not
`Admitted`, because their resource/heap/concurrent relations are not yet in the scaffold.
