# Sprint 05 report: surface language, elaborator, and `atli run`

## Plan and architecture

- Added `src/surface/`:
  - `lexer.rs`: hand-written lexer with spans, line comments, reduced-surface unsupported
    diagnostics, and token tests.
  - `parser.rs`: recursive-descent parser for the Sprint 05 subset of `docs/syntax.md`.
    First error stops; spans are precise.
  - `ast.rs`: span-carrying surface AST.
  - `pretty.rs`: pretty-printer for the implemented subset.
- Added `src/elaborate/`: surface AST to `core::Term`, plus a side-table mapping core
  term strings and variable occurrences to source spans. `core::Term` remains span-free.
- Added `src/diagnostics/`: one caret-rendering path for parse/elaborate/check errors.
- Added `src/bin/atli.rs` with `check`, `run`, and `core`.
- Added `examples/` programs before implementation: `fib`, `log2`, `server_loop`,
  `state_handler`, `default_handler`, `wedge`, and `unsupported`.
- Verified components (`core`, `interp`, `check`, `grade`, proofs) were consumed, not
  semantically modified.

## Surface-to-core mapping

`docs/elaboration.md` is the mapping spec for this sprint. Notable decisions:

- Files elaborate to nested core `let`s ending in `main`.
- Multi-argument calls are curried to the unary core.
- Decimal Nat literals elaborate to unary `zero`/`succ`.
- `case n { 0 -> e0 ; p -> e1 }` is the Nat eliminator; `p` binds the predecessor.
- `L.op(e)` elaborates to `perform ℓ e`; only `effect L { op(x: Nat) -> Nat }` is
  accepted.
- Handler continuation usage is parsed/elaborated even for wedges; `check::check` rejects
  §4.7 violations with source blame.

## Acceptance table

| # | Criterion | Result | Evidence |
|---|---|---:|---|
| 1 | Examples run | PASS | `fib`→`0`, `log2`→`0`, `state_handler`→`7`, `default_handler`→`9`, `server_loop` reports budget exhaustion as `Div`. |
| 2 | Wedge rejects with source blame | PASS | `atli check examples/wedge.atli` exits 1 with `Handle §4.7`, `extra-mention`, and a caret under `z = k`'s `k`. |
| 3 | Unsupported constructs diagnose | PASS | `unsupported.atli` reports `uniqueness ^ is not yet in the reduced surface`, exit 1. |
| 4 | Round-trip differential | PASS | Pretty/reparse/elaborate stability over runnable examples plus wedge; handler examples match hand-built core witnesses and values. |
| 5 | Witness surfacing | PASS | `atli check` prints type/effects/`β`/divergence; `server_loop` prints `β: ω` and `Div`. |
| 6 | `atli core` | PASS | Prints elaborated core and span table for every elaborable example; wedge appends the checker diagnostic after the core; unsupported input stops with its reduced-surface diagnostic. |
| 7 | Spec-gap ledger | PASS | Added surface arithmetic and measure-without-surface-checker gaps; elaboration mapping doc exists. |
| 8 | Regression | PASS | Rust suite, CLI/frontend tests, audit, and `make -C proofs` all green. |

## CLI output samples

```text
$ atli run examples/state_handler.atli
7
```

```text
$ atli check examples/server_loop.atli
type: Nat
effects: ∅
β: ω
divergence: Div
```

```text
$ atli check examples/wedge.atli
error: Handle §4.7 rejected `(let z = k in succ(succ(succ(succ(succ(succ(succ(succ(succ(zero))))))))))`: extra-mention: `k` appears free but is never directly resumed
 --> examples/wedge.atli:6:9
  |
 6 |     z = k
  |         ^
```

## Limitations carried forward

- Full arithmetic Fibonacci is blocked by the reduced core lacking arithmetic primitives;
  recorded as `SPEC-GAP(surface-arithmetic-reduced-core-gap)`. The committed `fib.atli`
  is a structural Nat recursion seed whose checked/run value is `fib(0) = 0`.
- `measure e` is parsed and conservatively screened, not surface-typechecked; recorded as
  `SPEC-GAP(surface-measure-typecheck-without-surface-checker)`.
- The span table is string-keyed rather than core-node-id-keyed. It is sufficient for this
  sprint's diagnostics and tested wedge path, but a future richer checker diagnostic API
  should carry stable blame ids.

## Verification commands

- `cargo fmt -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `make -C proofs`
- `just audit`
