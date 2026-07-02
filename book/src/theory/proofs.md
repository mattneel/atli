# Proof ladder

The Rocq scaffold lives under [`proofs/`](../../proofs/). Grade laws, substitution infrastructure, the mention⇔resume lemma, and step determinism have discharged rungs. `proofs/ADMITTED_COUNT` pins the current `Admitted.` count at 3; CI fails if it increases.


L9, uniqueness soundness (`inplace set` and in-place record replacement observationally equivalent to their functional-copy counterparts under affine ownership), is recorded as Stated-Pending-Infrastructure. It needs an aggregate heap and graded contexts in the Rocq step relation; it is not counted in `ADMITTED_COUNT`.


## Coverage boundary after v0.5.1

The Rocq scaffold still covers the reduced core. Generics, aggregates, uniqueness, and tasks are explicitly outside the mechanized fragment until a future proofs expansion; `ADMITTED_COUNT` remains 3.
