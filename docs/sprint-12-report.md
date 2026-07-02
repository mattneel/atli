# Sprint 12 Report — Records, Variants, and Structural Data

## Summary

Sprint 12 shipped v0.3.0 structured data: nominal monomorphic records and variants, record
literals/projection/update, constructor patterns, record patterns, destructure-consume for
unique aggregates, and structural recursion over constructor payloads. Task 0 also resolved
`pipe-inplace-composition`; `examples/render.atli` now uses the pitch `|> inplace … |> freeze`
form.

## Acceptance table

| Criterion | Result | Evidence |
|---|---:|---|
| Render pitch pipe form | Pass | `examples/render.atli`; `atli test examples/` |
| Calculus amendment before code | Pass | commit `05e1b74`; `ADMITTED_COUNT=3` |
| `shape_area.atli` flagship variant | Pass | oracle/native in `atli test examples/`; MLIR golden |
| `natlist.atli` structural `sum` without measure | Pass | finite β (`1`), oracle/native output `6`, MLIR recursive call golden |
| `mailbox.atli` destructure-consume | Pass | oracle/native output `42`; aggregate/in-place stores in MLIR golden |
| In-place record update | Pass | `record_update_inplace` uses `@atli_array_inplace_set`; functional twin uses copy-set |
| Negative diagnostics | Pass | `field_from_unique`, `use_after_destructure`, `nonexhaustive`, `inplace_shared_record`, `structural_bad_list` |
| Full accepted-example differential | Pass | `cargo run -- test examples/` |
| Regression | Pass | `cargo test` (16 unit + 16 frontend + 24 golden + 3 doctests) |

## Implementation notes

Aggregates lower to the tier-1 data region as handles: records are field-slot arrays;
variants are tag-plus-payload arrays. The oracle now allows arrays to hold arbitrary value
terms so record payloads can carry arrays/variants without inventing a second heap.
Functional update copies; `inplace` update emits a bare store after the surface affinity pass
consumes the unique handle.

The checker-facing core still has the pre-existing array handle representation, so the surface
elaborator and checker recognize constructor-pattern payloads as the strict-descent witnesses
for structural recursion over recursive variants. `solve.rs` was unchanged.

## Carried forward

Generics, path-`inplace`/borrow splitting, aggregate unboxing, RC/early reclamation, `spawn`,
WASM, and formal L9 proof infrastructure remain roadmap work.
