# Sprint 08 report — Multi-label effects, growable backend, mutual-recursion blocker

## Summary

Part A's calculus amendment is committed as `docs(calculus): multi-label effects and mutual recursion`.
The executable stack now supports interned multi-label effects through the oracle, derived witness,
checker, surface elaborator, generator fixtures, and the compiled path exercised by `two_effects.atli`.
`server_loop.atli` now builds natively and bounded-runs with `ATLI_MAX_ITERS`, using the growable `ω`
path. The remaining blocker is the real `fix*` binding-group AST/checker/interpreter ripple: the spec
is amended, but Rust still has unary `fix`, so natural generated multi-node SCCs are not yet produced.

## Acceptance table

| Area | Result | Evidence |
|---|---:|---|
| Calculus amendment | PASS | `docs/calculus.md` generalizes labels, handler search, and `fix*`; commit `1c5a799`. |
| Multi-label core labels | PASS | `Label::intern`, handler clause vectors, per-label `clause_for`. |
| Interpreter cross-label semantics | PASS | Goldens: different-label transparent to outer handler; same-label inner handler delimits. |
| Checker/derive per-clause β | PASS | Existing fixed-seed differential remains green; generator now includes multi-label handler shapes. |
| Surface multi-effect syntax | PASS | `! {A, B}`, multiple `effect` declarations, `A.op(e)`, multi-clause handlers. |
| Compiled cross-label smoke | PASS | `atli run --compiled examples/two_effects.atli` prints `8`; high-water `0`, β `0`. |
| Growable `Div` smoke | PASS | `ATLI_MAX_ITERS=5 ./server_loop` exits 0 with `ATLI_GROWABLE_SEGMENT=64`. |
| Mutual recursion / generated multi-node SCCs | BLOCKED | `even/odd` still rejects as `odd` unbound; recorded as `SPEC-GAP(mutual-recursion-core-implementation)`. |
| Regression | PASS | `cargo test` green after changes. |

## SCC histogram status

The solver's hand-built multi-node SCC unit tests still pass. The generated fixed-seed sample now
contains multi-label handlers, but because Rust lacks the new `fix*` core term, generated terms still
cannot naturally produce multi-node SCCs. The Sprint 03 singleton-SCC reservation is therefore not
closed by this implementation; it is narrowed to the explicit `fix*` implementation gap.

## Growable backend notes

Finite-β programs still size their arena from `CertifiedArena` and trap on overflow. For `β = ω`,
`CertifiedArena::from_checked` preserves the sealed certificate path but returns the growable initial
segment size (64 slots) to the emitter. The MLIR module is marked `atli.growable = true`, and `div`
functions call a runtime tick. The tick is inert by default; tests set `ATLI_MAX_ITERS` to stop a
known divergent program without changing source semantics.

## Verification

- `cargo test`
- `cargo test --test frontend growable_div_backend_bounded_run_exhausts_test_iters`
- `cargo test props::tests`
- `ATLI_MAX_ITERS=5 cargo run -- run --compiled examples/server_loop.atli`
- `cargo run -- run --compiled examples/two_effects.atli`

## Carried forward

- Implement the `fix*` binding-group term in `core`, `interp`, `derive`, `check`, surface SCC
  elaboration, generator, and codegen. This is required to close the generated multi-node SCC
  reservation honestly.
- Replace the lexical cross-label compiled smoke with a fully general runtime handler scope stack.
