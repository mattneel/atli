# Roadmap after v0.1.0

- **Uniqueness / `^` / `inplace` / `move`** — spend the existing `Q = {0,1,ω}` semiring in user-visible memory reuse. Blocks serious data-structure performance work.
- **`scope` / `spawn` concurrency** — spawn = arena = cancellation; depends on uniqueness and a richer region story.
- **WASM backend** — stack-switching where available, trampoline fallback otherwise; depends on the current split-frame representation stabilizing.
- **Byte-accurate frame refinement** — §9.1 pins slot units; variable-size activation backends still need the byte refinement.
- **Evidence passing / handler inlining** — tier-3 optimization replacing the runtime handler-scope stack where static evidence is profitable.
- **Rocq L3/L4/L7/L8 discharges** — progress, preservation, boundedness, and solver/certificate soundness move from ledger to theorem.
- **Real measure verification** — v0.1.0 trusts `measure`; future work checks well-founded measures instead of trusting the annotation.
- **De Bruijn proof representation decision** — named binders kept the bridge legible; deeper substitution proofs may force a de Bruijn refactor.
- **Multi-target releases** — Linux x86_64 ships first; macOS, Windows, and WASM release artifacts follow the backend work.
