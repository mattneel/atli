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

The point is not that nothing was wrong; the point is that every layer had another layer capable of catching it.
