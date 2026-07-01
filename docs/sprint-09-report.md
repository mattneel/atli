# Sprint 09 report — `fix*` ripple and runtime handler-scope stack

## Summary

Sprint 09 is complete. Part A implements `fix*` binding groups through the executable stack: core AST,
small-step oracle, derived witness, checker constraint emission, generator, surface SCC elaboration,
and native codegen. `examples/even_odd.atli` elaborates to `fix*`, checks with finite certified
`β = 2`, runs under the oracle, and compiles to mutually-recursive native functions that agree with
the oracle.

Part B replaces the compiled lexical handler smoke with a runtime handler-scope stack. Native `handle`
now emits scope records carrying label id, clause mode, and handler-entry watermark; `perform ℓ` in a
called function invokes `atli_scope_perform`, which walks those records innermost-out at runtime.
Lexically visible clauses still use the more precise existing `H-op-drop` / `H-op-resume` lowering,
with the L5 citation preserved for direct resume.

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
| Runtime handler-scope stack | PASS | `conditional_handler`, `handler_in_recursion`, and `drop_across_scopes` compile and match the oracle; IR goldens show `atli_scope_push`, `atli_scope_perform`, and `atli_scope_pop`. |
| Regression | PASS | Full Rust suite, clippy, and proofs green. |

## Generated SCC evidence

The fixed-seed generator includes measure-tagged two-member cycles. Solver statistics over the safe
generated sample:

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

## Runtime handler-scope stack

The native runtime stack record is:

```text
{ label_id: i64, mode: i64, value: i64, watermark: i64 }
```

Records live in the runtime shim outside the certified β arena. This is the Sprint 09 accounting
decision: handler-scope records are dynamic dispatch metadata, not continuation/activation frames in
§9.1's slot metric. The emitted IR passes the handler-entry high-water mark into each record; current
slot-frame instrumentation has no cumulative bump pointer to reset, but the watermark field is present
and golden-visible for the `H-op-drop` contract.

Forcing examples:

- `conditional_handler.atli`: installs a handler in a `case` branch; a called function performs under
  that runtime-selected scope. Oracle and compiled output: `5`.
- `handler_in_recursion.atli`: recursive function installs a handler at each level; performs in a
  callee find the innermost runtime scope. Oracle and compiled output: `0`, high-water `1 ≤ β 1`.
- `drop_across_scopes.atli`: an outer `B` handler catches a `B.op` through an intervening transparent
  `A` handler. Oracle and compiled output: `9`; IR shows scope push/pop and `H-op-drop` scope record.

## Verification

- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `make -C proofs`
- `cargo run -- run examples/even_odd.atli` → `1`
- `cargo run -- check examples/even_odd.atli` → `β: 2`, `Terminates`
- `cargo run -- run --compiled examples/even_odd.atli` → `1`, `ATLI_HIGH_WATER=1 ATLI_BETA=2`
- `cargo run -- run --compiled examples/conditional_handler.atli` → `5`
- `cargo run -- run --compiled examples/handler_in_recursion.atli` → `0`, `ATLI_HIGH_WATER=1 ATLI_BETA=1`
- `cargo run -- run --compiled examples/drop_across_scopes.atli` → `9`

## Carried forward

- The runtime stack currently supports the first-order Nat handler ABI used by the Sprint 09 fragment.
  Future tier-3 work can optimize this with evidence passing or handler inlining, but the semantic
  baseline is now dynamic handler search rather than lexical smoke.
