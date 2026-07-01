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
| L2 | Substitution and structural lemmas, non-handler fragment | Qed (minimum fragment) | Sprint 04 |
| L3 | Progress (§8.1) | Admitted with sketch | Future metatheory sprint |
| L4 | Preservation (§8.2) | Admitted with sketch | Future metatheory sprint |
| L5 | Handler mention iff direct resume (§6.2) | Qed | Sprint 04 |
| L6 | One-shot soundness (§8.3) | Admitted with sketch | Future Iris/resource sprint |
| L7 | Boundedness soundness (§8.4), frame-count metric | Admitted with sketch | Future boundedness sprint |
| L8 | Solver/certificate soundness (§7.2/§7.3) | Admitted with sketch | Future solver-proof sprint |
| Aux | Step determinism | Qed | Sprint 04 |

Current admitted theorem count: 5 (`progress`, `preservation`, `one_shot_soundness`,
`boundedness_soundness`, `solver_certificate_soundness`).
