# Sprint 12 Report — Records, Variants, and Structural Data

## Summary

Sprint 12 shipped structured data: nominal monomorphic records and variants, record
literals/projection/update, constructor patterns, record patterns, destructure-consume for
unique aggregates, and structural recursion over constructor payloads. Task 0 resolved
`pipe-inplace-composition`; `examples/render.atli` now uses the pitch `|> inplace … |> freeze`
form.

Completion repair: v0.3.0 was tagged with two prompt criteria omitted from this report's
acceptance table. The missing work landed in `b1146f9` and is released as v0.3.1. This report
now keys one row per numbered acceptance criterion, in order, so omission-class failures show
up as missing numbers instead of silent green tables.

## Acceptance table

| # | Criterion | Result | Evidence |
|---:|---|---:|---|
| 1 | `render.atli` uses multi-step `|> inplace … |> freeze`, runs both paths equal, `ATLI_DATA_ALLOCS=1`; pipe gap filed/resolved; blame headers no byte offsets | Pass | `examples/render.atli`; Task 0 commit `c1864e2`; `atli test examples/` |
| 2 | Calculus amendment before code; A.1–A.4 present; `ADMITTED_COUNT=3` | Pass | commit `05e1b74`; `proofs/ADMITTED_COUNT` |
| 3 | `shape_area.atli` is the syntax.md flagship variant snippet, both paths equal | Pass | `examples/shape_area.atli`; `tests/goldens/codegen/shape_area.mlir`; `atli test examples/` |
| 4 | `natlist.atli` structural `sum` accepted without `measure`, finite β, both paths equal; mistagged structural fold rejects | Pass | finite β `1`, output `6`; `examples/natlist.atli`; `examples/structural_bad_list.atli` |
| 5 | `mailbox.atli` both paths equal; IR shows destructure, in-place buffer store, repack; allocation counter golden'd | Pass | `examples/mailbox.atli`; `tests/goldens/codegen/mailbox.mlir`; `atli test examples/` |
| 6 | In-place record update emits a single store; functional twin allocates/copies; in-place allocates strictly fewer | Pass | `examples/record_update_inplace.atli`; `examples/record_update_functional.atli`; MLIR goldens |
| 7 | Four negatives reject with rendered diagnostics; destructure-consume blame is two-location; non-exhaustive lists missing constructors | Pass | `field_from_unique`, `use_after_destructure`, `nonexhaustive`, `inplace_shared_record`; frontend goldens |
| 8 | Record-shaped divergence falsifier demonstrates compiled ≠ oracle on bypassed alias/destructure/inplace program; accepted examples stay value-equal | Pass (completion `b1146f9`) | `codegen::tests::bypassed_record_destructure_aliasing_inplace_diverges_from_copy_oracle`; `cargo test` |
| 9 | Generator produces aggregate programs/tagged negatives; checker⇔derive verdict agreement exact over fixed-seed sample; coverage includes constructor-pattern descent both ways | Pass (completion `b1146f9`) | `props::generated_terms_satisfy_differential_acceptance_with_fixed_seed`; `props::fixed_seed_sample_has_required_coverage_and_distribution`; `props::generator_tagged_aggregate_negatives_match_frontend_verdicts` |
| 10 | `solve.rs` unchanged; protected logic unchanged except mechanical aggregate arms; proofs unchanged except L9 clause; pre-existing β values unchanged; regression green | Pass | `git diff v0.2.0 -- src/check/solve.rs` empty during Sprint 12; `cargo test`; `make -C proofs` |
| 11 | Book chapter live; syntax/elaboration/ROADMAP updated; v0.3.x tagged and release green | Pass | `book/src/learning/structured-data.md`; v0.3.0 release; v0.3.1 completion tag |

## Finding: acceptance-table omission class

The v0.3.0 report omitted criteria 8 and 9 entirely: no row, no note, no spec-gap. The table
only claimed green rows for the criteria it contained, but a freely-composed table allowed two
numbered prompt criteria to disappear. This is finding twelve. The structural repair is now
project law in `CONTRIBUTING.md`: acceptance tables must include exactly one top-level row per
numbered prompt criterion, in order.

## Implementation notes

Aggregates lower to the tier-1 data region as handles: records are field-slot arrays;
variants are tag-plus-payload arrays. The oracle allows arrays to hold arbitrary value terms so
record payloads can carry arrays/variants without inventing a second heap. Functional update
copies; `inplace` update emits a bare store after the surface affinity pass consumes the unique
handle.

The checker-facing core still has the pre-existing array handle representation, so the surface
elaborator and checker recognize constructor-pattern payloads as strict-descent witnesses for
structural recursion over recursive variants. `solve.rs` was unchanged.

The completion commit extends the generator's fixed-seed space with structured-data encodings:
record construction/peek, functional and in-place record update, destructure-consume chains, and
a recursive variant-style structural fold. It also adds generator-owned tagged negative fixtures
for heap-field projection from unique records, use-after-destructure, non-exhaustive cases,
in-place update on shared records, and non-payload structural recursion.

## Verification

- `cargo test -q` — 18 unit/property + 16 frontend + 24 golden + 3 doctests green.
- Targeted completion checks: `fixed_seed_sample_has_required_coverage_and_distribution`,
  `generated_terms_satisfy_differential_acceptance_with_fixed_seed`,
  `generator_tagged_aggregate_negatives_match_frontend_verdicts`, and
  `bypassed_record_destructure_aliasing_inplace_diverges_from_copy_oracle` all green.

## Carried forward

Generics, path-`inplace`/borrow splitting, aggregate unboxing, RC/early reclamation, `spawn`,
WASM, and formal L9 proof infrastructure remain roadmap work.
