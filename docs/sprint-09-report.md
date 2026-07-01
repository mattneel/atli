# Sprint 09 report — `fix*` ripple and handler-scope-stack status

## Summary

Part A's `fix*` binding-group ripple is implemented through the executable stack: core AST,
small-step oracle, derived witness, checker constraint emission, generator, surface SCC
elaboration, and native codegen. `examples/even_odd.atli` now elaborates to `fix*`, checks with
finite certified `β = 2`, runs under the oracle, and compiles to mutually-recursive native
functions that agree with the oracle.

Part B's real runtime handler-scope stack is not implemented in this pass. Sprint 08's lexical
compiled handler smoke remains the carried-forward codegen limitation; the ADR/report ledger keeps
that limitation explicit rather than relabeling the existing static dispatch as dynamic scope.

## Acceptance table

| Area | Result | Evidence |
|---|---:|---|
| Core `fix*` AST + pretty printer | PASS | `Term::FixGroup` and `FixBinding`; `atli core examples/even_odd.atli` prints both entries. |
| Interpreter group unfold | PASS | Goldens: `fix_group_even_odd_unfolds_and_evaluates`, `fix_group_three_member_cycle_evaluates`. |
| Derived witness | PASS | `derive_witness` handles group members; fixed-seed differential remains green. |
| Checker constraints | PASS | `infer_fix_group` emits per-member unknowns; structural cyclic groups reject with §4.8/§7.1 blame. |
| Solver unchanged | PASS | No changes to `src/check/solve.rs`; Tarjan/iterate/widen accepted natural group constraints. |
| Generator multi-node SCCs | PASS | Fixed seed: 956 safe terms; SCC histogram `{1: 743, 2: 68}`. |
| Surface SCC elaboration | PASS | Top-level declaration SCCs elaborate to `fix*`; forward references in cyclic groups are legal. |
| Native mutual recursion | PASS | `atli run --compiled examples/even_odd.atli` prints `1`; IR golden contains calls between `@atli_fn_even` and `@atli_fn_odd`. |
| Runtime handler-scope stack | PENDING | Lexical dispatch code remains; see carried-forward note below. |

## Generated SCC evidence

The fixed-seed generator now includes measure-tagged two-member cycles. Solver statistics over the
safe generated sample:

- Safe accepted generated terms: `956 / 1024`
- SCC size histogram: `{1: 743, 2: 68}`
- Iterations-to-convergence histogram: `{2: 654, 7: 157}`

This resolves the six-sprint singleton-SCC reservation for the checker/generator path: generated
terms now naturally exercise multi-node SCCs without hand-built solver fixtures.

## `even_odd` witness story

`examples/even_odd.atli`:

```text
fn even(n: Nat) -> Nat measure n = case n { 0 -> 1; p -> odd(p) }
fn odd(n: Nat) -> Nat measure n = case n { 0 -> 0; p -> even(p) }
fn main() -> Nat = even(4)
```

The surface declaration call graph has one two-node SCC, so elaboration produces `fix*` projections
for both `even` and `odd`. The checker accepts the measure-tagged cycle, solves the group constraints
through the existing SCC solver, and reports:

```text
type: Nat
effects: ∅
β: 2
divergence: Terminates
```

A structural version of the same cycle is rejected with `FixGroup-Structural §4.8/§7.1`, naming the
cross-member call and explaining that cyclic groups require `measure` or `div`.

## Handler-scope stack status

The real dynamic handler-scope stack remains to be implemented and is recorded as
`SPEC-GAP(runtime-handler-scope-stack-codegen)`. The current compiled path still uses
source-structure-aware handler lowering for the examples it supports; it has not been replaced by a
runtime stack carrying `{label-set, clause dispatch info, arena watermark}`. Scope-record accounting
therefore remains undecided for codegen. The next codegen sprint should begin with the ADR 0003
second amendment required by Sprint 09 Part B, including whether scope records live inside or outside
the certified arena.

## Verification

- `cargo test --lib props::tests::fixed_seed_sample_has_required_coverage_and_distribution`
- `cargo test --test golden fix_group`
- `cargo run -- run examples/even_odd.atli` → `1`
- `cargo run -- check examples/even_odd.atli` → `β: 2`, `Terminates`
- `cargo run -- run --compiled examples/even_odd.atli` → `1`, `ATLI_HIGH_WATER=1 ATLI_BETA=2`

Full-suite verification is recorded in the final turn for this work.

## Carried forward

- Replace the lexical compiled handler dispatch with the real runtime handler-scope stack from
  `docs/calculus.md §5`, with explicit scope-record accounting in ADR 0003.
