# Proof ladder

The Rocq scaffold lives under [`proofs/`](../../proofs/). Sprint 15 moves the ledger:
effectful progress, preservation with row/bound order, and solver/certificate soundness
are `Qed`; boundedness soundness is the single remaining `Admitted` theorem, now stated
over an instrumented frame-step relation.

`proofs/ADMITTED_COUNT` pins the current `Admitted.` count at 1. CI requires an exact
match, so any future movement up or down must update the file and the report ledger in the
same commit.

L6, L9, and L10 remain Stated-Pending-Infrastructure. L9 needs a heap plus graded data
contexts; L10 needs a concurrent small-step relation over task pools. The recommended next
proof increment is the graded-context + heap infrastructure, because it supports both L9
and the resource accounting needed for L6.

## Coverage boundary after v0.5.2

The Rocq scaffold still covers the reduced core. Generics, aggregates, uniqueness, and
tasks are explicitly outside the mechanized fragment until a future proofs expansion.
