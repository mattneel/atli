# Proof ladder

The Rocq scaffold lives under [`proofs/`](../../proofs/). v0.5.3 supersedes v0.5.2's
previously false proof-ledger claim: the semantic `step` relation is restored to the
honest `stepf t = Some u -> step t u` relation, and bridge anchors now make self-loop
degeneracy uncompilable.

v0.5.4 pins `proofs/ADMITTED_COUNT` at 1: `boundedness_soundness` (L7) is the sole
`Admitted`. `progress` (L3), `preservation` (L4), and `solver_certificate_soundness` (L8)
are `Qed` over the deep continuation semantics: captured contexts, `capture`/`plug`,
`ctx_types`, and latent `Cont` bounds are all load-bearing.

L8's honesty note matters. The record-level `solver_certificate` statement is
ω-degenerate by `solver_certificate_only_omega` because the record is not parameterized by
its solved constraint system. The real content is the §7.2 functional-model surface:
`solve_model_postfix`, `converged_least`, `pass_extensive`, `wpass_extensive`,
`beval_monotone`, and `certified_read_is_evaluation`.

The recommended next proof increment is L7: prove the frame metric invariant that a finite
certified β bounds every `frame_max_run` prefix. After that, graded contexts plus heap
infrastructure unlock the L9/L6 work.

## Coverage boundary after v0.5.4

The Rocq scaffold still covers the reduced core. Generics, aggregates, uniqueness, and
tasks remain outside the mechanized fragment until a future proofs expansion; this is the
coverage line carried from the proof ledger, not an `Admitted` theorem.
