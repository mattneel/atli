# Findings history

The executable-spec loop audited the paper spec and implementation repeatedly:

1. Nat elimination was needed for structural recursion to have teeth.
2. Pure recursion was invisible to the original frame-count metric.
3. Handler drop accounting overcharged dropped continuations.
4. Mention-without-resume exposed the need for the §4.7 side condition.
5. The solver certificate seam allowed uncertified maps until sealed.
6. Vacuous Rocq L6/L7 statements were demoted pending infrastructure.
7. L8 needed a true-solution hypothesis.
8. Sprint 06's MLIR artifact was a summary, not load-bearing lowering.
9. Multi-node SCCs needed real `fix*` implementation evidence.
10. Lexical handler dispatch needed the runtime handler-scope stack.
11. README quickstart transcripts hand-typed `β: 1`; the no-rot script now executes and diffs them.
12. Pipe-into-prefix composition routed around the pitch `|> inplace` form until fixed.
13. Sprint 12 acceptance tables omitted numbered criteria; CONTRIBUTING now requires one row per criterion.
14. Aggregate generator coverage initially fired from plain array encodings; Sprint 13 made it falsifiable.
15. Aggregate affinity remains single-implementation after surface lowering; ROADMAP names the two closure routes.
16. Sprint 13 v0.4.0 task runtime overclaimed: spawn used a no-op pthread hook, child arenas were not allocated, and the race falsifier was hand-C. v0.4.1 replaces it with `atli_spawn`/`atli_await`, per-task β operands, thread-ID telemetry, and an actual-shim MLIR falsifier.

The point is not that nothing was wrong; the point is that every layer had another layer capable of catching it.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.1 tasks

Structured concurrency is load-bearing in v0.4.1. The scheduler-independence claim is tested by accepted examples and attacked by the race falsifier; the formal L10 concurrent small-step proof remains pending infrastructure.


## v0.5.0 generics

No new finding is introduced by Sprint 14. The release extends the differential chain with generic examples, an erasure golden, fixed-seed coverage tags for generic instantiation and both `^u` grades, and a provenance-pinned `^u` privilege falsifier.


## v0.5.4 the induction, decomposed

Sprint 16 split the proof summit into small rungs and let each rung test the semantic
substrate before the headline theorems were attempted.

- Finding 21: continuation payload erasure hid the real handler and captured context; `TContVal h ctx`, `capture`, `plug`, and deep resume repaired §5.
- Finding 22: handler `p`/`k` aliasing split static lookup from dynamic substitution; the mechanized resuming rule now has an explicit freshness premise.
- Finding 23: `stepf` pattern absorption dropped beta/case-succ congruences and used off-grammar fallbacks; value-guarded dispatch now matches `interp.rs`.
- Finding 24: fix `f`/`x` aliasing replayed the handler binder bug at §4.8; fix rules now require distinct binders.
- Finding 25: fix typing bound `f` at the wrong arrow; the mechanized core takes the equality slice of `β ⊒ Fix_β`.
- Finding 26: Rust solver widening escaped a partial SCC iterate; the corrected solver iterates widened passes to a post-fixpoint.
- Finding 27: `solver_certificate` is system-unparameterized and therefore ω-degenerate; the real L8 content lives in the §7.2 functional-model lemmas.
- Finding 28: the proof bridge transcribed the frame metric as a flat charge; `frame_max_run` now matches the Rust `max_frame` captured-depth metric.

Five of the eight were live counterexamples to the very theorems being proven, surfaced by
decomposition before the summit was attempted — the induction was never impossible, it was
undecomposed.
