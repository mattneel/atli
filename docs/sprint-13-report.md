# Sprint 13 Report — `scope`/`spawn`: The Tree of Arenas

## Summary

Sprint 13 implements the task forms already amended into the calculus: `scope`, `spawn`, and `await`. The oracle semantics is sequential and deterministic; native lowering now runs spawned callees on pthread-backed task records, allocates each child control arena from the callee certified β, returns results through `atli_await`, and exposes `ATLI_TASKS_SPAWNED` plus `ATLI_TASK_TIDS`. The accepted examples are schedule-independent by construction, and the bypassed race falsifier demonstrates the failure mode the checker prevents.

Task 0 landed first in `3c2a729`: aggregate coverage tags now depend on aggregate-origin markers, the disabled-aggregate red path is tested, and the aggregate-discipline single-implementation status is disclosed in the Sprint 12 amendment and ROADMAP.

## Acceptance table

| # | Criterion | Status | Evidence |
|---|---|---:|---|
| 1 | Task 0 merged first; aggregate coverage assertion falsifiable; single-implementation disclosure and ROADMAP entry exist | Pass | Commit `3c2a729`; `props::aggregate_coverage_assertion_is_falsifiable_when_aggregate_cases_are_disabled`; `docs/sprint-12-report.md`; `ROADMAP.md` |
| 2 | Calculus amendment before code; A.1–A.5 present; `ADMITTED_COUNT` 3 | Pass | Commit `2251b1b`; `docs/calculus.md §3/§4.5.3/§5/§9.3/§10`; `grep -R "Admitted\." proofs/theories | wc -l` → 3 |
| 3 | `fanout.atli` both paths equal; N≥10 native determinism smoke with N recorded | Pass | Previously false in `v0.4.0`: the old path only spawned a no-op pthread. Completion `56aa070` runs spawned callees through `atli_spawn`/`atli_await`; `task_examples_report_spawn_counts_and_are_deterministic` runs compiled `fanout` 10 times, one stdout set, `ATLI_TASKS_SPAWNED=3`, and `ATLI_TASK_TIDS` has ≥2 distinct IDs. |
| 4 | `courier.atli` both paths equal; no-copy-at-spawn evidence and task count committed | Pass | Previously incomplete in `v0.4.0`: the child body did not run on the spawned thread. Completion `56aa070` lowers `spawn process(move m)` to `atli_spawn(fn_ptr, arg, beta, growable)` and `await` to `atli_await`; compiled stderr has `ATLI_DATA_ALLOCS=2 ATLI_TASKS_SPAWNED=1` and distinct root/child TIDs. |
| 5 | `nursery.atli` and `worker_budget.atli` both paths equal/budget-equivalent; dropped-handle join demonstrated | Pass | `examples/nursery.atli` expects `6`; `examples/worker_budget.atli` uses `ATLI_MAX_ITERS=5` and compiled stderr contains `ATLI_MAX_ITERS exhausted`; `atli test examples/` green |
| 6 | Child control arenas sized from certified grades through typed API; compile-fail family covers raw arena path; IR shows per-task β constant | Pass | Previously false in `v0.4.0`: no child arena was allocated. Completion `56aa070` adds `CertifiedTaskBudget`, a compile-fail doctest, and MLIR goldens showing `llvm.mlir.addressof @atli_entry_*` plus literal callee β/growable operands passed to `atli_spawn`. |
| 7 | Four negatives reject with rendered diagnostics; cross-spawn double-use and effectful-spawn blame are present | Pass | `examples/double_await.atli`, `unique_to_two_spawns.atli`, `spawn_effectful.atli`, `handle_escapes_scope.atli` headers all pass under `atli test examples/`; byte-offset leakage removed from reuse headline |
| 8 | Race falsifier demonstrates native ≠ oracle and native nondeterminism across repeated runs; accepted sweep stays equal | Pass | Previously overclaimed in `v0.4.0`: the falsifier was hand-C. Completion `56aa070` builds a checker-bypass MLIR twin of `unique_to_two_spawns.atli`, links it against the actual generated `target/atli/runtime.c`, asserts native output differs from the copy oracle `0`, and observes ≥2 outputs over 40 runs. |
| 9 | Generator produces scope/spawn programs and tagged negatives with falsifiable tags; checker⇔derive agreement exact | Pass | `CoverageTag::{Scope,Spawn,Await}` in fixed-seed sample; `generated_terms_satisfy_differential_acceptance_with_fixed_seed` and coverage tests green |
| 10 | `solve.rs` unchanged; protected logic unchanged except mechanical arms; proofs unchanged except L10; pre-existing β values unchanged; full regression green | Pass | `src/check/solve.rs` untouched; `make -C proofs`; `cargo test`; `cargo clippy --all-targets -- -D warnings`; fib still reports `β: 2` |
| 11 | Book chapter live; syntax §9 promoted; elaboration/ROADMAP updated; `v0.4.1` tagged and release green | Pass | `book/src/learning/tasks.md`; `docs/syntax.md §9`; `docs/elaboration.md`; `ROADMAP.md`; `v0.4.1` is the honest completion tag after the runtime correction. |

## Verification commands

- `cargo fmt --all -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `cargo run --bin atli -- test examples/`
- `make -C proofs`
- `scripts/check-readme-quickstart.sh`

## Notes

- Finding sixteen: `v0.4.0` shipped rows 3/4/6/8 over a no-op task hook and hand-C falsifier. Completion `56aa070` replaces that with a real runtime: `atli_spawn(fn_ptr, arg, beta_slots, growable) -> handle`, `atli_await(handle) -> result`, thread-local control-arena/high-water state, generated function-pointer wrappers, and actual-shim checker-bypass MLIR falsification.
- Cross-task effect handlers, closure spawning, zero-copy heap results, cooperative cancellation, and M:N scheduling remain ROADMAP items; the one-thread-per-spawn runtime is intentionally simple but now load-bearing.
