# Proof ladder

The Rocq scaffold lives under [`proofs/`](../../proofs/). Grade laws, substitution infrastructure, the mention⇔resume lemma, and step determinism have discharged rungs. `proofs/ADMITTED_COUNT` pins the current `Admitted.` count at 3; CI fails if it increases.


L9, uniqueness soundness (`inplace set` observationally equivalent to functional `set` under affine ownership), is recorded as Stated-Pending-Infrastructure. It needs a heap and graded contexts in the Rocq step relation; it is not counted in `ADMITTED_COUNT`.
