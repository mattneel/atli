# Roadmap after v0.2.0

- **`^u` uniqueness polymorphism and generics** — v0.2.0 has monomorphic `^Array`; reusable unique containers need type parameters and uniqueness variables.
- **RC / early reclamation** — v0.2.0 data regions free at program exit; Perceus-style reuse/RC is the next memory-lifetime refinement.
- **Capture-rule relaxation** — unique captures are banned in tier 1; once-called closures would allow a more precise rule.
- **k/data-affinity unification** — continuation one-shot and data uniqueness are parallel 1-grading implementations today; the research endgame is one kinded row for effects, β-constraints, and uniqueness.
- **`scope` / `spawn` concurrency** — spawn = arena = cancellation; depends on uniqueness and a richer region story.
- **WASM backend** — stack-switching where available, trampoline fallback otherwise; depends on the current split-frame representation stabilizing.
- **Byte-accurate frame refinement** — §9.1 pins slot units; variable-size activation backends still need the byte refinement.
- **Evidence passing / handler inlining** — tier-3 optimization replacing the runtime handler-scope stack where static evidence is profitable.
- **Rocq L3/L4/L7/L8 discharges** — progress, preservation, boundedness, and solver/certificate soundness move from ledger to theorem.
- **Real measure verification** — v0.2.0 still trusts `measure`; future work checks well-founded measures instead of trusting the annotation.
- **De Bruijn proof representation decision** — named binders kept the bridge legible; deeper substitution proofs may force a de Bruijn refactor.
- **Multi-target releases** — Linux x86_64 ships first; macOS, Windows, and WASM release artifacts follow the backend work.
