# Atli

Atli is a functional systems-language experiment where the type checker computes the frame allocation used by native code. Source parses to a verified core, the checker seals a boundedness witness `β`, and the MLIR backend allocates exactly that many frame slots for finite programs while the oracle interpreter remains the semantic reference.

```text
.atli source → parse → elaborate → check / β-certificate → oracle run
                                                   └────→ MLIR/native run
```

## Quickstart

```sh
cargo build
cargo run -- run examples/fib.atli
# 55

cargo run -- check examples/fib.atli
# type: Nat
# effects: ∅
# β: 2
# divergence: Terminates

cargo run -- run --compiled examples/fib.atli
# 55
# stderr: ATLI_HIGH_WATER=1 ATLI_BETA=2 ATLI_DATA_ALLOCS=0 ATLI_TASKS_SPAWNED=0
```

Run the full example differential:

```sh
cargo run -- test examples/
```

## What v0.4.0 includes

- Surface parser, elaborator, diagnostics, and `atli` CLI.
- Unary `Nat`, monomorphic `Array`, unique `^Array`, `move`/`inplace`/`freeze`, functions, `case`, arithmetic prelude, `measure`/`div`, multi-label effects, handlers, mutual recursion (`fix*`), structured data, and `scope`/`spawn`/`await`.
- Reference interpreter and native MLIR→LLVM backend.
- A graded checker with sealed solver certificates: public consumers can read β only after SCC fixpoint solving completes.
- Runtime handler-scope stack, growable `div` path, task spawn reporting, overflow trap (86), one-shot debug trap (87), bounds trap (88), high-water reporting, and data allocation reporting.
- Rocq scaffold with the grade laws/substitution infrastructure/mention⇔resume lemma/step determinism work represented, and CI pinning the remaining admitted-count ledger.

## Grades as codegen licenses

| The checker proves… | …so native code may | Empirical gate |
| --- | --- | --- |
| finite `β` | allocate exactly `β` frame slots | high-water ≤ β; corrupted-β trap fires |
| `β = ω` / `Div` | use the growable segment | `server_loop` bounded-run smoke |
| handler clause drops `k` | skip continuation materialization | drop-handler IR goldens |
| handler clause resumes `k` once | omit release used-flag checks | wedge rejection + debug trap |
| multi-label effect rows | dispatch to innermost dynamic scope | forced-dynamic vs fast-path differential |
| unique `^Array` | lower accepted `inplace set` to a store | oracle/native value equality; allocation counter drops |
| affine task handles + move-only data | run spawned work with schedule-independent observables | fanout N=10 determinism smoke; race falsifier |

## The credibility feature

Fifteen findings were caught by the executable-spec loop: calculus gaps, handler accounting bugs, proof-ledger dishonesty, fake MLIR, missing `fix*`, and lexical handler dispatch. The history is documented in [the Book](book/src/theory/findings.md) and the sprint reports.

## Documentation

- [The Atli Book](book/src/SUMMARY.md) — tutorial, reference, theory narrative, project discipline.
- [`docs/calculus.md`](docs/calculus.md) — formal core and backend contract.
- [`docs/syntax.md`](docs/syntax.md) — implemented surface subset and open list.
- [`docs/elaboration.md`](docs/elaboration.md) — surface-to-core mapping.
- [`ROADMAP.md`](ROADMAP.md) — the second act.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — completion contract and engineering law.

## License

Dual-licensed under MIT or Apache-2.0; see [`LICENSE-MIT`](LICENSE-MIT) and [`LICENSE-APACHE`](LICENSE-APACHE).
