# Roadmap after v0.5.0

- **RC / early reclamation** — v0.2.0 data regions free at program exit; Perceus-style reuse/RC is the next memory-lifetime refinement.
- **Capture-rule relaxation** — unique captures are banned in tier 1; once-called closures would allow a more precise rule.
- **k/data-affinity unification** — continuation one-shot and data uniqueness are parallel 1-grading implementations today; the research endgame is one kinded row for effects, β-constraints, and uniqueness.
- **M:N scheduler and cooperative cancellation** — v0.4.1 uses one pthread per task and process-fatal traps; work stealing and structured failure propagation are next runtime refinements.
- **WASM backend** — stack-switching where available, trampoline fallback otherwise; depends on the current split-frame representation stabilizing.
- **Byte-accurate frame refinement ⇒ monomorphization** — §9.4 makes erasure sound only while every value is one slot; byte-sized activations make β type-dependent and trigger monomorphized codegen.
- **Evidence passing / handler inlining** — tier-3 optimization replacing the runtime handler-scope stack where static evidence is profitable.
- **Rocq L3/L4/L7/L8 discharges** — progress, preservation, boundedness, and solver/certificate soundness move from ledger to theorem.
- **Real measure verification** — v0.2.0 still trusts `measure`; future work checks well-founded measures instead of trusting the annotation.
- **De Bruijn proof representation decision** — named binders kept the bridge legible; deeper substitution proofs may force a de Bruijn refactor.
- **Multi-target releases** — Linux x86_64 ships first; macOS, Windows, and WASM release artifacts follow the backend work.

## After v0.5.0

- Zero-copy task result transfer: v0.4.1 copies heap results at `await`; region promotion would remove that copy.
- Cross-task effect handlers: spawned functions must handle their own effects today; inherited handlers across task stacks need new continuation semantics.
- Closures in `spawn` and task handles in data structures: both require extending the scope-locality rules.
- Row polymorphism: target signature `map[A, B](xs: List[A], f: A -> B ! e) -> List[B] ! e`; open rows need a row-unification sprint.
- Bounded polymorphism / traits: nothing currently needs `A: Eq`, but generic algorithms will.
- Reading-B revisit: bare parameters remain shared (`ω`) in v0.5.0; `^u` solves the combinator-doubling problem explicitly.
- Heap-ness-aware generic payload grading: v0.5.0 conservatively treats generic payloads as heap-like when destructuring/projecting unique aggregates.
- Mechanized-core coverage: Rocq still covers the reduced core, excluding generics, aggregates, uniqueness, and tasks until a proofs expansion sprint.
- Path `inplace` / borrow splitting: allow safe mutation through aggregate paths (`r.buf`) without destructuring the whole aggregate.
- Aggregate layout optimization: unbox small records/variants when it preserves the data-region and uniqueness contracts.
- Independent aggregate discipline: Sprint 13 disclosed that aggregate affinity is single-implementation after surface lowering; close this either with core-level aggregate terms or a second checker/derive-style discipline over the lowered encodings.
