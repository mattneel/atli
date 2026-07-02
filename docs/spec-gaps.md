# Atli spec gaps surfaced by executable sprints

This file records `SPEC-GAP:` findings exposed while turning the calculus into executable
Rust. The implementation chooses conservative interpretations and does not silently expand
semantics.

- SPEC-GAP(solver-certificate-record-system-unparameterized): the Rocq
  `solver_certificate` record quantifies its postfix/upper fields over all constraints
  rather than a carried system, so only the ω certificate inhabits it
  (`solver_certificate_only_omega`); finite Rust certificates are unrepresentable in the
  record, and the L8 record-level statement is degenerately true. Sprint 16 D2 proves the
  algorithmic §7.2 conjuncts over the explicit-system functional model instead;
  parameterizing the record by its constraint system is future work (finding
  twenty-seven).

- SPEC-GAP(handler-binder-aliasing-static-dynamic-split): `docs/calculus.md §4.7`
  writes handler clauses with distinct metavariables `pᵢ`/`kᵢ` and never states the
  distinctness side condition a named-binder implementation needs. With
  `op_param = op_k`, the mechanized typing context binds k innermost (k wins
  statically) while `subst2` substitutes the parameter first (param wins dynamically):
  `THandle (TPerform L TZero) (Handler "r" (TVar "r") L "k" "k" (TResume (TVar "k") TZero))`
  is closed, well-typed, and steps to the untypable stuck term `TResume TZero TZero` --
  a live counterexample to L4 as stated (finding twenty-two). The Rust
  checker/interpreter pair shares the same split (`check/mod.rs` binds k after param;
  `interp.rs` substitutes param first). Sprint 16 A6 repairs the mechanized side
  conservatively: resuming handler typing rules require `op_param ≠ op_k`, making
  aliased resuming clauses ill-typed. The Rust-side repair (checker rejection of
  aliased clauses) is carried-forward work.

- SPEC-GAP(fix-binder-aliasing-static-dynamic-split): `docs/calculus.md §4.8`'s
  `fix f. λx. e` uses distinct metavariables `f`/`x`; the mechanized rules bound the
  parameter innermost (param wins statically) while unfold substitutes the function
  name (func wins dynamically). `TFix "f" "f" TyNat (TVar "f") Structural` was
  closed, well-typed, and stepped to a wrongly-typed lambda -- a second live L4
  counterexample (finding twenty-four, the finding-twenty-two pattern at §4.8).
  Sprint 16 repairs the mechanized side conservatively with an `f ≠ x` premise on all
  three fix rules. The Rust checker types fix through a dedicated RecContext rather
  than shadowed env bindings; a surface-level probe of aliased fix names is
  carried-forward work.

- SPEC-GAP(fix-recursive-binding-row-mistranscription): `docs/calculus.md §4.8` binds
  `f` at the declared arrow `(T₁ →[σ] T₂)` -- the same `σ` as the conclusion -- with
  side condition `σ' ⊑ σ`; the mechanized rules bound `f` at a hardwired pure arrow
  (Structural/Measure) or left the premise row unconstrained under an `ω` conclusion
  (Div). Without subsumption this falsified preservation at unfold:
  `TFix "f" "x" TyNat TZero Div` typed at the `ω`-arrow but unfolded to a lambda typable
  only at the `0`-arrow (finding twenty-five). Sprint 16 repairs to the equality slice of
  `β ⊒ Fix_β(f,e)`: binding, body row, and conclusion latent coincide; the `⊑` slack is
  deferred with §4.9 subsumption/§8.6 to the future principality sprint. Conservative
  consequence: a `Div`-tagged fix must have a genuinely `ω`-row body; pure-body div fixes
  are rejected (the paper accepts them as imprecision).

- SPEC-GAP(deep-handler-resume-accounting-recursive): under §5's deep reinstallation,
  `resume` re-enters the handle, so a resuming clause's continuation bound must cover the
  rebuilt handle's whole demand: `β_k ⊒ β ⊕ (β_r ⊔ (βᵢ ⊕ β))`, §6.2's
  `β ⊒ c ⊕ β_rec` stated in-rule. `ω` is always admissible (§2.3's safe direction), while
  a finite `β_k` exists exactly when the residual context and clause costs ground at zero.
  The mechanized core now types `Cont` with a latent bound and constrains it in-rule. The
  Rust checker still under-approximates deep-handler re-entry: `src/check/mod.rs` infer
  for `Resume` charges only the argument, `Type::Cont` carries no bound, and handle
  computes the literal `βᵢ ⊕ β`. This is the §2.3 miscompile direction; checker
  alignment is carried-forward work.

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

- RESOLVED(solver-widening-partial-iterate-escape): `docs/calculus.md §7.2` step 3
  promises widening over-approximates upward, and §7.3 promises no partial iterate
  reaches consumers. The implementation's single widen pass could leave an SCC partner at
  a stale finite value below its ω-widened peer: `a ⊒ b ⊕ 1, b ⊒ a` gave `a = ω, b = 3`
  with `b ⊒ a` violated. That was an under-approximating certificate, §2.3's miscompile
  direction (finding twenty-six, found while building Sprint 16 D's Rocq solver model).
  The fix iterates the widened pass to stability; the regression test pins
  post-fixpoint-ness across the SCC. The Rocq D-rungs model the corrected algorithm.

- RESOLVED(stepf-pattern-absorption-congruence-loss): Sprint 16 finding twenty-three
  repaired the mechanized `stepf` dispatch. The beta and case-succ patterns had absorbed
  their congruence cases, so a lambda-headed application with a reducible argument and a
  succ-headed scrutinee with a reducible inside were `stepf`-stuck; the App/Resume
  congruence arms also carried an off-grammar stuck-function fallback. All three diverged
  from `docs/calculus.md §5`'s `E e | v E` / `case E` grammar and from the Rust oracle's
  value-guarded dispatch (`src/interp.rs`). Both absorption witnesses were well-typed,
  closed, non-value, un-blocked, `stepf`-stuck terms: live counterexamples to the corrected
  L3 trichotomy. The repair restructures the three dispatches to the oracle's
  value-guarded form; Bridge anchors pin the restored congruences and removed fallback.

- RESOLVED(mechanized-token-continuation-erasure): Sprint 16 Part A repairs Sprint 04's
  erased token continuation model. Continuation values now carry the installed handler and
  captured context as `TContVal h ctx`; `capture` decomposes handler bodies; §5's deep
  `H-op-resume`/rebuild dynamics are represented directly; and A6 adds `ctx_types`,
  `Ty_ContVal`, and `Ty_Resume` rules over a `Cont` type with its latent boundedness
  component. The old `TContVal (id : nat)` identity-resume counterexample is no longer the
  mechanized semantics.

- RESOLVED(definition-integrity-step-degeneracy): v0.5.2 falsely claimed L3/L4/L8
  discharge after changing the mechanized `step` relation into a self-loop observable for
  stuck terms. v0.5.3 restores `step` to the sole honest `StepByFunction : stepf t = Some u
  -> step t u`, adds relation falsifiability anchors in `Bridge.v`, and restores the proof
  ledger to the true admitted count.

- RESOLVED(mechanized-arrow-latent-erasure): Finding nineteen corrected the Rocq typing
  model back toward `docs/calculus.md §3.1/§4.2/§4.3`: arrows carry latent effect and
  boundedness rows. The previous `TyArrow a b` erased the lambda/fix body row, allowing
  `(λx. d) 0` to type at finite/pure judgment and step to a `Div` or effectful body.
  `Syntax.v` now represents `TyArrow a ε β b`, `Ty_Lam` stores the body row in the arrow,
  `Ty_App` charges the latent row, and fix rules form pure function values with latent
  bodies.

- RESOLVED(progress-open-effects): Finding eighteen corrected `docs/calculus.md §8.1`
  from classic effect-closed progress to the effectful trichotomy. A closed term with a
  nonempty row may be blocked on an unhandled operation, and the row must predict the
  label. The effect-closed corollary recovers classic value-or-step progress for empty
  rows, including spawned task bodies.

- RESOLVED(preservation-statement-drift): Finding eighteen also aligned §8.2 and
  `Meta.v`'s intended L4 with the ladder claim: preservation carries explicit effect-row
  subsumption and boundedness over-approximation (`ε' ⊆ ε`, `β' ⊑ β`) rather than merely
  preserving typability.

- RESOLVED(generic-arrow-instantiation): Sprint 14 originally claimed higher-order
  generic calls but `list_map.atli` did not exercise the quoted capability. The surface
  unifier defaulted generic variables in arrow positions instead of recursing through
  `A -> B`, so `fn map[A, B](xs: List[A], f: A -> B) -> List[B]` failed at the point a
  function argument was supplied. v0.5.1 resolves this by structurally unifying arrow
  types, adding the exact `map` signature as the flagship example, and pinning `apply` as
  a separate golden for generic function arguments.

- RESOLVED(pipe-inplace-composition): Sprint 12 fixes the Sprint 11 surface mismatch where
  the pitch form `buf |> inplace set(i, v)` rejected and `render.atli` used let-chaining
  instead. Pipe desugaring now threads the left-hand expression into the application inside
  prefix forms: `x |> inplace f(args)` becomes `inplace f(x, args)`, and `x |> freeze` /
  `x |> move` become `freeze x` / `move x` per `docs/syntax.md §5` and
  `docs/elaboration.md`.

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
