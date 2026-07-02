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
