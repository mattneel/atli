# Proof ladder

The Rocq scaffold lives under [`proofs/`](../../proofs/). v0.5.3 supersedes v0.5.2's
previously false proof-ledger claim: the semantic `step` relation is restored to the
honest `stepf t = Some u -> step t u` relation, and bridge anchors now make self-loop
degeneracy uncompilable.

`proofs/ADMITTED_COUNT` pins the current `Admitted.` count at 4: `progress`,
`preservation`, `boundedness_soundness`, and `solver_certificate_soundness`. The
effect-closed progress corollary, step determinism, relation anchors, and frame-step
erasure are `Qed`.

L6, L9, and L10 remain Stated-Pending-Infrastructure. The recommended next proof
increment is still graded contexts + heap infrastructure, because it supports both L9 and
the resource accounting needed for L6.

## Coverage boundary after v0.5.3

The Rocq scaffold still covers the reduced core. Generics, aggregates, uniqueness, and
tasks are explicitly outside the mechanized fragment until a future proofs expansion.
