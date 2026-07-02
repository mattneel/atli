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

The point is not that nothing was wrong; the point is that every layer had another layer capable of catching it.


## v0.3.0 structured data

Records and variants are implemented in v0.3.0. Normative syntax and lowering remain in `docs/syntax.md`, `docs/elaboration.md`, and `docs/calculus.md`; this Book chapter links the live examples rather than restating the rules.


## v0.4.0 tasks

Structured concurrency is implemented in v0.4.0. The scheduler-independence claim is tested by accepted examples and attacked by the race falsifier; the formal L10 concurrent small-step proof remains pending infrastructure.
