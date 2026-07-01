# Sprint 07 report: real MLIR lowering + compiled effect handlers

## Part A: finding-eight repair

Sprint 06's native execution path proved the β-sized-arena thesis through generated C,
but its `atli emit` MLIR was only a summary of the oracle-computed result. Sprint 07
replaced that with load-bearing MLIR:

- `src/codegen` emission no longer calls the oracle interpreter and no longer stores an
  `expected_output` field.
- `atli build` emits `.mlir`, lowers it through `mlir-opt` and `mlir-translate`, then links
  LLVM IR with a runtime shim.
- `tests/goldens/codegen/fib.mlir` contains recursive `func.call @atli_fn_fib` operations,
  the β comparison in `atli_touch_frame`, and no `arith.constant 55` answer paste.
- `RESOLVED(tier1-mlir-artifact-was-summary-not-lowering)` records the repair.

Pipeline per ADR 0003 amendment:

```text
mlir-opt --convert-scf-to-cf --convert-cf-to-llvm --convert-func-to-llvm \
         --convert-arith-to-llvm --finalize-memref-to-llvm \
         --reconcile-unrealized-casts
mlir-translate --mlir-to-llvmir
clang-22 program.ll runtime.c -o program
```

## Part B: compiled handlers

Tier-1 now compiles finite-β single-label handlers. The implementation strategy is a
lexical CPS/defunctionalized tier: because the reduced core has one statically known label,
`perform L.op` dispatches to the nearest compiled handler without a runtime handler stack.
This is not the final tier-2 design for multiple labels or dynamic handler scopes, but it is
the exact reduced-core shape needed for §5 `H-op-drop`/`H-op-resume`.

- Drop path: `H-op-drop` emits the operation clause body and abandons the captured context;
  the dropped clause contains no `atli_touch_frame` materialization. `default_handler.mlir`
  pins the frame-free comment and code shape.
- Resume path: `H-op-resume` emits a direct continuation shape and a debug one-shot check.
  The static dispatch comment cites `L5_mentions_iff_resume`, the Rocq lemma licensing FV
  dispatch on checked clauses.
- Debug one-shot trap: release examples pass silently; a corrupted IR test changes the
  resume-use constant and exits 87 with `ATLI ONE-SHOT VIOLATED`.

## Acceptance table

| # | Criterion | Result | Evidence |
|---|---|---:|---|
| A1 | No oracle in emission | PASS | `grep -rn "interp::eval\|expected_output" src/codegen/` is empty. |
| A2 | Real fib MLIR | PASS | `fib.mlir` has `func.call @atli_fn_fib`, β compare, no `arith.constant 55`. |
| A3 | Effect-free differentials | PASS | Existing compiled/oracle differential cases still pass through MLIR→LLVM→clang. |
| A4 | C harness deleted | PASS | Program logic is in MLIR; the remaining runtime shim only wraps main, reports high-water, and traps. |
| B1 | Handler examples compile | PASS | `state_handler`→7, `default_handler`→9, `counter`→3, `abort`→9 compiled outputs match oracle. |
| B2 | Drop frame-free | PASS | `default_handler.mlir` shows `H-op-drop` and no clause-local frame touch. |
| B3 | Resume round-trips | PASS | `counter.atli` performs/resumes through recursion three times; high-water 1 ≤ β 1. |
| B4 | One-shot debug trap | PASS | Corrupted resume-use IR exits 87 with `ATLI ONE-SHOT VIOLATED`. |
| B5 | β agreement extends | PASS | Every compiled handler program has an IR arena constant equal to checker-certified β and high-water ≤ β. |
| B6 | Fragment boundary | PASS | `server_loop.atli` remains rejected: `Div functions require the growable backend — tier 2`. |
| B7 | Regression | PASS | Rust tests, doctests, clippy, and proofs are green. |

## High-water / β table

| Program | Output | High-water | β |
|---|---:|---:|---:|
| `fib.atli` | 55 | 1 | 2 |
| `arith.atli` | 14 | 0 | 0 |
| `log2.atli` | 0 | 1 | 1 |
| `state_handler.atli` | 7 | 0 | 0 |
| `default_handler.atli` | 9 | 0 | 0 |
| `counter.atli` | 3 | 1 | 1 |
| `abort.atli` | 9 | 1 | 1 |
| `h_resume_add` | 6 | 0 | 0 |
| `h_drop` | 5 | 0 | 0 |
| `h_case_resume` | 3 | 0 | 0 |
| `h_case_zero` | 8 | 0 | 0 |
| `h_block_resume` | 8 | 0 | 0 |
| `h_block_drop` | 4 | 0 | 0 |

Drop-heavy programs remain tight at β 0 when no recursion occurs. `abort.atli` shows a
nontrivial high-water from `burn(3)` before the dropped operation, while the dropped clause
itself allocates no additional continuation frame.

## What this sets up

- Tier 2: dynamic/multi-label handler stacks and a growable `Div` backend.
- A richer continuation-frame layout for arbitrary captured locals; the current tier uses
  the reduced single-label lexical continuation shape.
- Future proof work can use the emitted slot-level frame operations as the concrete target
  for the L7 instrumented semantics.

## Verification commands

- `grep -rn "interp::eval\|expected_output" src/codegen/`
- `cargo fmt -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `cargo test --doc`
- `make -C proofs`
- `just audit`
