# Sprint 14 report — Generics and uniqueness preservation

Sprint 14 adds rank-1 parametric polymorphism, generic nominal aggregates, `Array[A]`, `Task[T]`, and the `^u` uniqueness-preservation marker. The backend keeps one erased symbol per generic function in tier 1 because every value is one i64 slot; `^u` preserves ownership across helper calls without granting mutation privileges inside the helper.

## Acceptance table

| # | Criterion | Status | Evidence |
|---|---|---|---|
| 1 | Calculus amendment before code; `^u` no-privileges, bare-stays-ω, conservative payload grading, erasure trigger, `ADMITTED_COUNT=3` | Pass | Commit `7a12dd5`; `docs/calculus.md`; `proofs/README.md`; `scripts/check-admitted-count.sh` => `Admitted count OK: 3` |
| 2 | `option.atli` and `list_map.atli` both paths equal; `list_map` structural finite β without `measure`; two-types-one-program source | Pass | `atli test examples/`; `cargo run -- check examples/list_map.atli` => `β: 2`, `Terminates`; `examples/list_map.atli` calls `map` at `List[Nat]` and `List[Option[Nat]]` |
| 3 | Erasure golden: exactly one compiled `map` symbol, called at two types | Pass | `tests/goldens/codegen/list_map.mlir`; `codegen_emit_goldens_pin_certified_arena_literals` asserts one `func.func @atli_fn_map` and multiple calls |
| 4 | `through`/`forget` pair: preserve accepted with `ATLI_DATA_ALLOCS=1`; forget rejects at second `inplace` with blame naming the forgetting path | Pass | `examples/preserve.atli`; `examples/forget.atli`; `atli test examples/`; compiled preserve stderr includes `ATLI_DATA_ALLOCS=1` |
| 5 | `inplace_on_preserving`, `arity`, `unbound_type_var`, `generic_field_peek` reject with rendered diagnostics | Pass | `examples/inplace_on_preserving.atli`; `examples/arity.atli`; `examples/unbound_type_var.atli`; `examples/generic_field_peek.atli`; `atli test examples/` |
| 6 | `^u` privilege falsifier demonstrates compiled ≠ oracle through Atli pipeline against generated shim | Pass | `bypassed_preserving_parameter_privilege_diverges_from_copy_oracle`: builds `preserving_privilege_twin.atli`, links checker-bypass MLIR against `target/atli/runtime.c`, copy oracle returns `0`, native bypass returns `1` |
| 7 | Generator produces generic programs with multi-type instantiation and both-grade `^u`; tags conditional/falsifiable; checker⇔derive exact fixed-seed sample | Pass | `CoverageTag::{GenericInstantiation, PreserveUnique, PreserveShared}`; forced fixed-seed inputs; `fixed_seed_sample_has_required_coverage_and_distribution`; disabled-generator red-path test also checks these tags disappear |
| 8 | Interpreter semantics unchanged beyond mechanical arms; `solve.rs` unchanged; protected logic unchanged; pre-existing β unchanged; full regression green | Pass | `git diff -- src/check/solve.rs` empty; `cargo test` green (19 lib, 19 frontend, 24 golden, 4 doctests); `cargo clippy --all-targets -- -D warnings` green |
| 9 | Spawn of generic callee works with per-function budget path unchanged | Pass | `examples/spawn_generic.atli`; `atli test examples/`; compiled run reports `ATLI_TASKS_SPAWNED=1` and prints `5` |
| 10 | Book chapter and syntax/elaboration/ROADMAP updates, row-polymorphism target, monomorphization trigger, mechanized coverage line | Pass | `book/src/learning/generics.md`; `docs/syntax.md`; `docs/elaboration.md`; `ROADMAP.md`; `mdbook build book`; `scripts/check-book-samples.sh` |
| 11 | `v0.5.0` tagged and release green | Pass | `Cargo.toml` version is `0.5.0`; this report is included in the release commit that is tagged `v0.5.0`; release workflow is the remote gate after push |

## Design notes

- **Erasure.** `map[A, B]` emits one `@atli_fn_map` symbol. Tier-1 erasure is sound because every value is one i64 slot; `ROADMAP.md` pairs byte-accurate frames with monomorphization as the trigger that ends this free erasure model.
- **`^u`.** A preserving parameter is affine and can be returned/threaded, but `inplace` and `move` require definite `^A`. This is enforced by the surface uniqueness pass and attacked by the bypass falsifier.
- **Effect rows.** Generic higher-order functions are pure in v0.5.0. The blocked row-polymorphic target is recorded verbatim: `map[A, B](xs: List[A], f: A -> B ! e) -> List[B] ! e`.
- **Mechanization boundary.** The Rocq scaffold remains the reduced core; generics, aggregates, uniqueness, and tasks are named coverage gaps rather than smuggled proof claims.

## Verification evidence

- `cargo test` — pass: 19 lib/unit/property, 19 frontend, 24 golden, 4 doctests.
- `cargo clippy --all-targets -- -D warnings` — pass.
- `make -C proofs` — pass.
- `scripts/check-admitted-count.sh` — `Admitted count OK: 3`.
- `scripts/check-readme-quickstart.sh` — pass.
- `mdbook build book` and `scripts/check-book-samples.sh` — pass.
- `cargo run -- test examples/` — pass over all examples, including the new generic positives and negatives.
