# Sprint 06 report: arithmetic prelude + β becomes an allocation

## Part A: arithmetic prelude

- Implemented `+`, `-`, and `*` in the parser with `*` over left-associative `+`/`-`
  (`docs/syntax.md §1`).
- Elaborated operators to injected unary-`Nat` library recursion, only when used:
  `__atli_add`, `__atli_sub`, `__atli_mul`, plus private `__atli_pred` for monus.
- Resolved `SPEC-GAP(surface-arithmetic-reduced-core-gap)`: primitive arithmetic is a
  backend performance decision, not a core semantic extension.
- `examples/fib.atli` is now real Fibonacci and needs `measure n`: the recursive calls are
  `fib(m)` and `fib(m - 1)`, and the second is a prelude call rather than the peeled
  predecessor itself. Under the strict structural rung, real textbook fib is therefore not
  accepted as `Structural`; this is the first concrete algorithmic pressure point for the
  boundedness discipline. The checked witness is `β = 2`, `Terminates`.

## Part B: frame model

- Added `docs/calculus.md §9.1`: β counts frame slots, not bytes; tier 1 uses i64 slots;
  arena overhead `C = 0`; certified overflow traps.
- Narrowed `SPEC-GAP(frame-metric-byte-accuracy)`: the slot unit is now pinned, while
  byte refinement for variable-size backend frames remains open.
- Updated the Rocq L7 pending-infrastructure comment to cite the §9.1 slot metric.

## Part C: tier-1 native lowering

- Added ADR 0003 choosing textual MLIR artifacts plus external LLVM/MLIR 22.1.8 tooling.
- Added `src/codegen/` for the effect-free, finite-β, first-order-Nat fragment.
- Added `atli emit`, `atli build`, and `atli run --compiled`.
- The emitter API accepts `CertifiedArena`, built only from `check::CheckedWitness`'s
  `CertifiedGrade`; a compile-fail doctest proves callers cannot size an arena from a raw
  integer.
- Native code uses a certified arena slot constant, reports high-water use on stderr, and
  traps with `ATLI ARENA OVERFLOW: certified beta violated` if a frame claim exceeds β.

## Acceptance table

| # | Criterion | Result | Evidence |
|---|---|---:|---|
| A1 | Real fib under oracle | PASS | `atli run examples/fib.atli` prints `55`; `atli check` reports `β: 2`, `Terminates`. |
| A2 | Arithmetic examples | PASS | `examples/arith.atli` prints `14` and injects only the used arithmetic prelude functions. |
| B1 | Frame unit pinned | PASS | `docs/calculus.md §9.1`, gap narrowed, `proofs/theories/Meta.v` L7 comment updated. |
| C1 | Compiled correctness differential | PASS | 13 effect-free finite programs in `tests/frontend.rs` compare oracle vs compiled stdout. |
| C2 | β arena literal | PASS | `tests/goldens/codegen/fib.mlir` shows `atli.certified_beta_slots = 2`; `arith` shows `0`. |
| C3 | High-water ≤ β | PASS | Compiled differential parses `ATLI_HIGH_WATER`/`ATLI_BETA` from every native run. |
| C4 | Trap works | PASS | Unit test corrupts β from `1` to `0`; native harness exits 86 with the overflow message. |
| C5 | Gate extension | PASS | `src/codegen/mod.rs` compile-fail doctest prevents raw-integer arena construction. |
| C6 | Fragment diagnostics | PASS | `state_handler.atli` says effects/handlers are Sprint 07; `server_loop.atli` says Div needs growable backend. |
| C7 | Regression | PASS | Rust tests, doctests, clippy, proofs, and `just audit` run in verification. |

## High-water / β table

| Program | Output | High-water | β |
|---|---:|---:|---:|
| `fib.atli` | 55 | 1 | 2 |
| `arith.atli` | 14 | 0 | 0 |
| `log2.atli` | 0 | 1 | 1 |
| `const0` | 0 | 0 | 0 |
| `const7` | 7 | 0 | 0 |
| `add` | 13 | 0 | 0 |
| `sub1` | 3 | 0 | 0 |
| `sub_monus` | 0 | 0 | 0 |
| `mul` | 42 | 0 | 0 |
| `prec` | 14 | 0 | 0 |
| `block_case` | 6 | 0 | 0 |
| `struct` | 0 | 1 | 1 |
| `measure` | 0 | 1 | 1 |

The finite β values are tight for `arith`/non-recursive programs and recursive countdowns.
Real fib is slack by one slot (`1/2`): the current §7 `Measure` rung pays an annotation
cost for the recursive algorithm even though the tier-1 first-order frame claim is one
slot. That is a precision finding, not a soundness issue.

## Toolchain note

The emitted MLIR is a valid, reviewable artifact carrying the certified arena literal; the
native Sprint 06 harness compiles generated C with `clang-22`/`clang` to keep handler,
continuation, and dialect lowering out of scope. This is intentionally narrow and recorded
in ADR 0003. Sprint 07+ should make the MLIR artifact the compilation input when the
runtime dialect is introduced.

## Verification commands

- `cargo fmt -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `cargo test --doc`
- `make -C proofs`
- `just audit`
