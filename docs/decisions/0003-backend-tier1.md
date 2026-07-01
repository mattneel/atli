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
