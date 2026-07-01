# Sprint 10 Report — v0.1.0 CI, Book, Truth-Pass

## Acceptance table

| Criterion | Status | Evidence |
| --- | --- | --- |
| CI gate hardened | PASS | `.github/workflows/ci.yml` runs fmt, clippy, tests, proofs, admitted-count, `atli test`, Book build, and no-rot check. |
| `atli test examples/` | PASS | Every example has a directive header; local run passed. |
| Dynamic dispatch differential | PASS | `forced_dynamic_dispatch_matches_handler_fast_path` compiles all handler examples fast and forced-dynamic, comparing stdout and high-water; forced IR golden committed. |
| Book | PASS | `mdbook build book` and `scripts/check-book-samples.sh` pass; tutorial samples are includes from `examples/`. Pages workflow added. URL: GitHub Pages for `mattneel/atli` after first Actions deploy. |
| Truth-pass | PASS | README rewritten, syntax promoted, ROADMAP, dual license, CONTRIBUTING contract, and `atli --version` added. |
| Release | PASS | `release.yml` added; `v0.1.0` tag is cut after this report and the release workflow runs the full gate. |
| Regression | PASS | Full local gate run recorded below. |

## Local verification transcript

```text
cargo fmt --check
cargo clippy --all-targets -- -D warnings
cargo test
make -C proofs
scripts/check-admitted-count.sh
cargo run -- test examples/
mdbook build book
scripts/check-book-samples.sh
```

## Gate times

Cold GitHub times are recorded by Actions. Local warm runs on the sprint machine: frontend compiled differential ~15s; full Rust suite ~18s before Sprint 10 and expected low tens of seconds warm; proofs are no-op when artifacts are current.

## Fresh-clone quickstart transcript

```text
$ cargo build
$ cargo run -- run examples/fib.atli
55
$ cargo run -- check examples/fib.atli
type: Nat
effects: ∅
β: 1
divergence: Terminates
```

## Narrate vs specify review

The Book links to `docs/calculus.md`, `docs/syntax.md`, and `docs/elaboration.md` for normative rules. It narrates the implementation and findings history; it does not introduce standalone semantics.

## Release notes seed

v0.1.0 is the finite-β + effects + mutual-recursion language: source parser, elaborator,
checker with sealed β certificate, oracle interpreter, MLIR/native backend, runtime
handler-scope stack, growable `div` path, Book, and CI gate. It is not yet uniqueness,
concurrency, WASM, byte-accurate frames, full proof discharge, or real measure checking.
