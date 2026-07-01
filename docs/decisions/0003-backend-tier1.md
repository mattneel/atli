# ADR 0003: Tier-1 backend toolchain

## Status

Accepted for Sprint 06.

## Decision

Use **textual MLIR emission plus external LLVM/MLIR tools** as the tier-1 backend route.
The pinned toolchain is LLVM/MLIR **22.1.8** with `clang-22`, `mlir-opt`, and
`mlir-translate` from the LLVM 22 package set. The local development package version is
`1:22.1.8~++20260613092238+e80beda6e255-1~exp1~20260613092253.78`; LLVM's release
schedule lists 22.1.8 as the June 16, 2026 point release, and the official release page
publishes 22.1.8 binary artifacts.

## Rationale

- Textual MLIR is a readable artifact. `atli emit` can be golden-tested and reviewed.
- External tools avoid binding Atli to a Rust MLIR wrapper version during the compiler's
  first lowering sprint.
- The emitted module carries the certified arena size as a literal MLIR attribute, keeping
  the allocation evidence inspectable.
- The native Sprint 06 build driver uses a tiny generated C harness compiled by `clang-22`
  for the effect-free finite fragment while preserving the MLIR artifact as the committed
  intermediate. This keeps the first native path small and keeps handler/continuation
  lowering out of scope.

## Consequences

- `atli emit` requires no external tool.
- `atli build` prefers `ATLI_CLANG`, then `clang-22`, then `clang`; if no compiler exists,
  codegen integration tests skip with a loud notice.
- CI should install the LLVM 22 package set (`clang-22`, `mlir-22-tools`,
  `llvm-22-tools`) and run the codegen differentials. Local contributors without LLVM can
  still run the Rust/proof suites.
- Direct LLVM IR emission remains out of scope; when MLIR lowering grows beyond the
  current tier-1 harness, the MLIR module becomes the compilation input rather than only
  the reviewable artifact.

## Sources

- LLVM release schedule, 22.1.x series: https://llvm.org/
- LLVM 22.1.8 release assets: https://github.com/llvm/llvm-project/releases/tag/llvmorg-22.1.8

## Sprint 07 amendment: MLIR is load-bearing

Sprint 07 repairs the Sprint 06 deviation where the generated C harness was the real
compiler and `atli emit` was a summary constant. The invariant is now: **the MLIR module
is the compilation input; no emission path calls the oracle interpreter; the oracle only
verifies compiled behavior after the fact.**

The emitted dialect mix is `func`, `arith`, `scf`, and `memref`, lowered by:

```text
mlir-opt --convert-scf-to-cf --convert-cf-to-llvm --convert-func-to-llvm \
         --convert-arith-to-llvm --finalize-memref-to-llvm \
         --reconcile-unrealized-casts
mlir-translate --mlir-to-llvmir
clang-22 program.ll runtime.c -o program
```

The arena/high-water state lives in the MLIR module as `memref.global` data, and the β
comparison operand is emitted in MLIR by `atli_touch_frame`. The runtime shim is not a
compiler: it only wraps `main`, prints the result/high-water, and provides overflow and
one-shot trap functions.

Handler lowering strategy for Sprint 07 is a first defunctionalized/CPS-shaped tier: the
single lexically known label lets `perform` dispatch statically to the nearest handler.
`H-op-drop` abandons the captured continuation without frame materialization; `H-op-resume`
compiles the direct resume as a call back into the captured continuation shape. Tier 2 must
generalize this to multi-label/dynamic handler stacks.

## Sprint 09 second amendment: runtime handler-scope stack

Sprint 09 replaces the lexical handler-dispatch smoke with a minimal runtime handler-scope stack for
native lowering of the current first-order fragment. Entering a `handle` emits one scope record per
operation clause:

```text
{ label_id: i64, mode: i64, value: i64, watermark: i64 }
```

The stack lives in the runtime shim rather than the certified β arena. Rationale: scope records are
control metadata for dynamic handler search, not continuation/activation frames counted by §9.1's
slot metric. The emitted IR still captures the arena high-water value at handler entry and passes it
into the record so drop clauses have the watermark needed by the §5 `H-op-drop` contract; the current
slot-frame backend has no cumulative bump pointer to reset, so the watermark is an observable
contract field rather than a byte-moving operation.

`perform ℓ` outside a lexically visible handler lowers to `atli_scope_perform(label_id(ℓ), arg)`,
which walks the runtime stack innermost-out. Lexically visible operations still use the existing
source-level lowering for precision: `H-op-drop` abandons the continuation path, and `H-op-resume`
uses the direct-resume lowering licensed by `L5_mentions_iff_resume`. The runtime ABI handles the
forcing case that lexical dispatch could not: a called function performing under a handler installed
by its caller. Tier-3 optimization may replace this with evidence passing or handler inlining, but the
semantic baseline is now dynamic scope search per `docs/calculus.md §5`.
