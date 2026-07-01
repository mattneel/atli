# Atli spec gaps surfaced by executable sprints

This file records `SPEC-GAP:` findings exposed while turning the calculus into executable
Rust. The implementation chooses conservative interpretations and does not silently expand
semantics.

- SPEC-GAP(frame-metric-byte-accuracy): Sprint 06 narrows this gap by pinning the unit
  of finite `β` in `docs/calculus.md §9.1`: `β` counts frame slots, and tier 1 defines one
  slot as one `i64` machine word with arena overhead `C = 0`. The remaining gap is byte
  refinement for future backends with variable-size activations or target-specific frame
  fields. Sprint 04's Rocq scaffold still does not state `L7` as a theorem: the
  instrumented slot-counting step relation is missing. When added, it should target the
  §9.1 slot metric; byte-accurate layout is a later backend refinement over that metric.

- SPEC-GAP(measure-tag-trusted-reduced-core): Sprint 03 accepts `Measure`-tagged `fix`
  terms as the annotated recursion rung but does not verify an actual well-founded
  measure. This is intentional for the reduced core: `docs/calculus.md §4.8/§7` keeps the
  solver architecture real while deferring real measure obligations to the future surface
  checker/elaborator. Sprint 04's `Typing.v` mirrors that trust boundary with a rule comment
  rather than adding an unproven measure checker to the mechanized core.

- SPEC-GAP(frame-metric-recursion-blindspot): the substitution-based reference interpreter
  reifies continuation frames only when a handler captures an operation context
  (`interp::decompose` → `alloc_continuation`). Pure recursion does not allocate an
  observable frame in `max_frame`, even though `docs/calculus.md §8.4` is about all
  continuation frames. Sprint 02 therefore checks handler-capture boundedness with
  `max_frame ≤ β` and checks the recursion half through the separate termination split:
  derived `Terminates` terms must reach `Value` within budget, while derived `Div` terms
  must exhaust the budget. This is honest differential coverage, not a complete frame
  layout model for recursion.



## Resolved gaps

- RESOLVED(runtime-handler-scope-stack-codegen): Sprint 09 replaces the compiled
  unhandled-perform path with a runtime handler-scope stack. Entering a native `handle`
  emits scope records keyed by interned label id with clause mode and entry watermark;
  `perform ℓ` in called functions invokes `atli_scope_perform`, which walks innermost-out
  at runtime. Lexically visible handler clauses still use the precise `H-op-drop`/
  `H-op-resume` lowering, while dynamic resuming clauses return through the runtime scope
  ABI. Goldens cover conditional installation, recursive installation, and drop-across
  transparent scopes.

- RESOLVED(mutual-recursion-core-implementation): Sprint 09 implements `fix*` binding
  groups through Rust core, interpreter, derived witness, checker, generator, surface
  elaboration, and native codegen. Surface declaration SCCs now elaborate to group
  projections, `even_odd.atli` runs under both oracle and compiled paths, and the fixed-seed
  generated sample produces natural multi-node solver SCCs (`{1: 743, 2: 68}`), closing the
  Sprint 03 singleton-SCC reservation with generated evidence.


- RESOLVED(multi-label-effects-reduced-core): Sprint 08 generalizes labels from the single
  `L` fixture to interned label identifiers. Core handlers carry clause vectors, the
  checker and derived witness compute per-clause `β̂ᵢ`, surface effect rows parse finite
  label lists, and the interpreter's `H-op` search treats nested handlers for other labels
  as transparent (`docs/calculus.md §5`). Goldens cover both transparent different-label
  nesting and same-label delimiting.

- RESOLVED(div-growable-backend-smoke): Sprint 08 removes the native-code diagnostic for
  `β = ω` programs. The compiled path now emits a growable module mode with an initial
  64-slot segment and a test-only `ATLI_MAX_ITERS` runtime tick; `server_loop.atli` builds
  and bounded-runs natively. This is a smoke growable backend, not a proof of variable-size
  frame layout.

- RESOLVED(tier1-mlir-artifact-was-summary-not-lowering): Sprint 06's native path used a
  generated C harness as the real compiler, while `atli emit` printed a summary MLIR module
  containing the oracle-computed answer as `arith.constant`. Sprint 07 replaces that
  summary with load-bearing MLIR: the MLIR module is the compilation input, no emission
  path calls the oracle interpreter, and `interp` is used only by differential tests after
  compiled execution.

- RESOLVED(handler-k-usage-discipline): `docs/calculus.md §4.7` now makes option (i)
  explicit: a handler clause may drop `k` only by not mentioning it, and if `k` appears
  free then the clause must contain exactly one direct `resume k v` and no other free
  occurrence of `k`. Thus `k ∈ FV(eᵢ) ⇔ eᵢ` resumes `k` for well-typed clauses, licensing
  the interpreter's lazy-capture FV dispatch while requiring the future checker to reject
  mention-without-resume wedges such as `let z = k in e`.

- RESOLVED(handler-drop-captured-frame-accounting): `docs/calculus.md §4.7` and §5 now use
  lazy continuation capture. A dropped operation clause (`k ∉ FV(eᵢ)`) reduces by
  `H-op-drop` without materializing the delimited continuation frame, so its effective
  `β̂ᵢ` is exactly the clause body's `βᵢ`. A resuming clause uses `H-op-resume`,
  materializes the one-shot continuation, and pays `βᵢ ⊕ β`. This preserves the
  exception/default-handler idiom where dropping is frame-free.

- RESOLVED(nat-structural-recursion-core): `docs/calculus.md` now includes unary `zero` /
  `succ e` naturals and `case e { zero => e₀ ; succ x => e₁ }`. The predecessor `x` in
  the `succ` branch is the strict subterm used by structural `Fix`; `gen.rs` derives
  finite `β` for recursive calls on that predecessor and `ω` for non-strict structural
  recursion.

- SPEC-GAP(surface-measure-typecheck-without-surface-checker): `docs/syntax.md §8` says
  the `measure e` expression should be meaningful at type `Nat`, but Sprint 05 still has
  no surface type checker. The elaborator conservatively accepts only a Nat literal or the
  unary Nat parameter as a measure expression before trusting the existing reduced-core
  `Measure` tag (`SPEC-GAP(measure-tag-trusted-reduced-core)`).

- RESOLVED(surface-arithmetic-reduced-core-gap): Sprint 06 implements `+`, `-`, and `*`
  as elaborator-injected library recursion over unary `Nat`, not core primitives. `-` is
  monus (truncated subtraction). Prelude functions are injected only when used; native
  primitive arithmetic is a backend performance decision, not a core semantic extension.
