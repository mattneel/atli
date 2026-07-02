# Sprint 11 Report — Uniqueness: Spending the Q Semiring

## Summary

Sprint 11 adds the first consumer of `Q = {0,1,ω}`: surface `^Array` handles are affine
(`Q::One`) and may be consumed by `move`, `inplace`, unique-parameter passing, or shared
forgetting. The minimal owned heap object is monomorphic `Array` of `Nat`; functional `set`
copies in both oracle and native code, while accepted `inplace set` lowers to a native bare
store with no data-region allocation. `β` remains a control-frame slot grade and is unchanged
for all pre-existing examples.

Task 0 landed first (`586a689`): README/sprint-10 quickstart `β` was corrected to 2 and
`scripts/check-readme-quickstart.sh` now executes the transcript, including the compiled
stderr line.

## Acceptance table

| Criterion | Status | Evidence |
| --- | --- | --- |
| Task 0 first, README no-rot | Pass | `scripts/check-readme-quickstart.sh` prints `README quickstart OK`; CI workflow invokes it. |
| Calculus amendment | Pass | `docs/calculus.md` has arrays (§3), affine discipline (§4), array reductions (§5), data region (§9.2), and L9 SPI (§10/proofs). `proofs/ADMITTED_COUNT` remains `3`. |
| `render.atli` oracle ⇔ compiled, one allocation | Pass | `atli run` and `run --compiled` both print `42`; compiled stderr `ATLI_DATA_ALLOCS=1`; `render.mlir` calls `@atli_array_inplace_set`. |
| `copy_vs_inplace` allocation differential | Pass | In-place compiled allocs `1`; functional compiled allocs `3`. |
| Negative uniqueness diagnostics | Pass | `use_after_move.atli`, `inplace_on_shared.atli`, and `captured_unique.atli` are `expect-check-error` examples. Double-use errors render the reuse site plus a note at first consumption. |
| Divergence falsifier | Pass | `codegen::tests::bypassed_aliasing_inplace_diverges_from_copy_oracle` compares the always-copy oracle result `0` against bypassed native aliasing mutation result `1`. |
| Bounds trap | Pass | `compiled_array_allocations_and_bounds_are_observable` verifies oracle `Outcome::BoundsTrap` and native exit 88 / `ATLI BOUNDS`. |
| Generator/checker differential | Pass | Fixed-seed sample includes `CoverageTag::Array`; checker⇔derive exact witness agreement remains green. Surface tagged negatives are covered by `atli test examples/`. |
| Guardrails | Pass with note | `solve.rs` unchanged; proofs unchanged except L9 ledger text. Continuation-k traversal arms were extended for new term variants, but the L5 predicate logic/dispatch classification was not refactored. |
| Book/docs/release | In progress in tree | Book chapter and reference updates added; final gate/tag performed after this report. |

## Data-region evidence

| Program | Oracle stdout | Compiled stdout | `ATLI_DATA_ALLOCS` | Notes |
| --- | ---: | ---: | ---: | --- |
| `examples/render.atli` | 42 | 42 | 1 | One `mkarray`, one accepted in-place store. |
| `examples/copy_vs_inplace.atli` | 2 | 2 | 1 | Two in-place updates; no copy allocation. |
| `examples/copy_functional.atli` | 2 | 2 | 3 | `mkarray` plus two functional `set` copies. |

IR goldens pin the distinction:

- `tests/goldens/codegen/render.mlir` contains `// inplace set, calculus.md §9.2` and
  `func.call @atli_array_inplace_set`.
- `tests/goldens/codegen/copy_functional.mlir` contains `func.call @atli_array_copy_set`.

## Diagnostics samples

`use_after_move.atli`:

```text
error: cannot use `a`: consumed here -> bytes 91..92; used again here -> bytes 99..100
 --> examples/use_after_move.atli:5:7
  |
 5 |   get(a, 0)
  |       ^
note: first consumption here
 --> examples/use_after_move.atli:4:12
  |
 4 |   b = move a
  |            ^
```

`inplace_on_shared.atli`:

```text
error: inplace requires unique `s`, but it is shared
 --> examples/inplace_on_shared.atli:5:19
  |
 5 |   b = inplace set(s, 0, 1)
  |                   ^
```

## Implementation notes

- The oracle keeps always-copy semantics for arrays, including `inplace set`; this is the
  semantic reference. Native code may mutate only after the surface uniqueness pass has
  consumed a `Q::One` binding.
- The current surface has no local lambda syntax, so a literal captured-unique source shape
  cannot be expressed yet. `captured_unique.atli` is therefore a double-consumption negative;
  `docs/elaboration.md` records that the tier-1 capture ban is a core/rule obligation until
  local closures land.
- `^u` uniqueness polymorphism, RC/early reclamation, capture-rule relaxation, and k/data
  affinity unification moved to `ROADMAP.md`.

## Verification

Executed during the sprint:

- `scripts/check-readme-quickstart.sh`
- `scripts/check-admitted-count.sh`
- `make -C proofs`
- `cargo test` (after code and golden updates)
- `mdbook build book && scripts/check-book-samples.sh`

Final full gate and release tag are performed after this report is committed.
