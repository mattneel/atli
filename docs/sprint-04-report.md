# Sprint 04 report: certificate sealing and Rocq scaffold

## Part A: certificate sealing

Commit: `033eb2e fix(check): seal solver certificate behind solve()`.

- Replaced the raw public solver values map with sealed `SolverCertificate` in
  `src/check/solve.rs`.
- `PendingGrade::certify` now consumes `&SolverCertificate`, not `&BTreeMap<UnknownId,
  Bound>`, so callers cannot mint certified grades from arbitrary maps.
- `SolverCertificate` has no public constructor and no mutable access to its values;
  tests can observe values only through `value(id)`. `SolverStats` remains public
  observability.
- Extended compile-fail documentation to cover both phase-gate seams: pending grades
  cannot construct `CheckedWitness`, and external code cannot construct
  `SolverCertificate`.

Part A verification before commit:

- `cargo fmt -- --check`
- `cargo test` (13 unit/property + 19 golden + 2 compile-fail doctests)
- `cargo clippy --all-targets -- -D warnings`

## Mechanization toolchain

Decision: plain Rocq/Coq now, no Iris dependency yet. See
`docs/decisions/0002-mechanization-toolchain.md`.

Pinned build used by this sprint and CI:

- `coqc` 8.18.0
- OCaml 4.14.1
- Ubuntu Noble package `coq=8.18.0+dfsg-1build2`

Rationale: the required Sprint 04 `Qed` obligations are syntactic/algebraic and do not
need Iris yet; the proof tree is structured so Iris can be introduced later for
one-shot/resource proofs.

## Proof scaffold

Added `proofs/`:

- `Grade.v`: §2 grade carriers and laws.
- `Syntax.v`: reduced §3/§10 syntax, named binders, substitution, FV/resume counters,
  plus a runtime-only used-continuation marker for the deliberate resume-after-use stuck
  state.
- `Typing.v`: §4 typing skeleton including amended §4.7 Handle side condition and lazy
  `β̂ᵢ` cases.
- `Step.v`: §5 small-step function/relation including `case-zero`, `case-succ`,
  `H-return`, `H-op-drop`, `H-op-resume`, one-shot continuation values, and the
  resume-after-use stuck state.
- `Solve.v`: §7.1 constraint expressions and a certificate record stating the sealed
  post-fixpoint invariant that Part A enforces at the Rust API boundary.
- `Meta.v`: proof ladder statements.
- `Bridge.v`: seven golden-term transcriptions/verdict checks.

Build command: `make -C proofs`.

## Proof ladder table

Exact admitted theorem count after ledger repair: 3. L6/L7 are explicitly demoted to
`Stated-Pending-Infrastructure` until their resource/frame-count definitions exist.

| Rung | Theorem family | Sprint 04 status | Evidence |
|---|---|---:|---|
| L1 | Grade algebra laws | Qed | `Grade.v` proves Q semiring laws, Eff join laws, Bound `⊕`/`⊔`/order laws. |
| L2 | Substitution/structural lemmas | Qed (minimum) | `L2_substitution_nonhandler_min` / `substitution_preserves_unmentioned_typing`. |
| L3 | Progress (§8.1) | Admitted | `Meta.v` statement with sketch/owner. |
| L4 | Preservation (§8.2) | Admitted | `Meta.v` statement with sketch/owner. |
| L5 | Mention iff direct resume (§6.2) | Qed | `handler_clause_ok_mentions_iff_resumes` and `L5_mentions_iff_resume`. |
| L6 | One-shot soundness (§8.3) | Stated-Pending-Infrastructure | No theorem placeholder; missing continuation resource/usage transition model is named in `Meta.v`. |
| L7 | Boundedness soundness (§8.4) | Stated-Pending-Infrastructure | No theorem placeholder; missing instrumented frame-counting step relation is named in `Meta.v`. |
| L8 | Solver/certificate soundness (§7.2/§7.3) | Admitted | `solver_certificate_soundness` stated; certificate field projection is Qed. |
| Aux | Step determinism | Qed | `step_deterministic` / `step_is_deterministic`. |

## Golden-term bridge

`Bridge.v` transcribes seven existing golden shapes and checks Rocq verdicts matching the
Rust checker/spec fences:

| Golden shape | Rocq result | Rust-side expectation |
|---|---:|---|
| Mention-without-resume wedge (`let z = k in zero`) | rejected (`handler_clause_ok = false`) | checker rejects §4.7 wedge |
| Dropped handler body | accepted (`handler_clause_ok = true`) | dropped clause accepted, lazy capture |
| Resuming handler body | accepted (`handler_clause_ok = true`) | resuming clause accepted |
| Extra double resume body | rejected (`handler_clause_ok = false`) | one-shot discipline rejects |
| Nested dropped handler body | accepted (`handler_clause_ok = true`) | nested handler/drop fixture accepted |
| Structural fix over peeled predecessor | typable | structural golden accepted |
| Div fix | typable as `BOmega` | div golden accepted/classified `Div` |

No bridge mismatches were found.

## Carried-forward limitations and gaps

- The Sprint 03 solver-coverage reservation remains: generated reduced-core terms still
  cannot create multi-node SCCs because the core has no mutual recursion. Multi-node SCC
  behavior is exercised by hand-built solver goldens/proofs only until a future core
  extension introduces a natural generated source.
- `SPEC-GAP(frame-metric-byte-accuracy)` remains open. Rocq `L7` is not yet a theorem
  statement; it is pending the instrumented frame-counting relation, which should target
  the interpreter's frame-count proxy before any byte-layout refinement.
- `SPEC-GAP(frame-metric-recursion-blindspot)` remains open; recursion boundedness is
  still witnessed by termination/divergence classification rather than a recursive frame
  metric.
- `SPEC-GAP(measure-tag-trusted-reduced-core)` remains open; `Typing.v` mirrors the
  reduced-core trust boundary and does not add a measure checker.
- No new Sprint 04 spec gaps were surfaced.

## CI

Updated `.github/workflows/ci.yml` with a `proofs` job on `ubuntu-24.04` that installs
`coq=8.18.0+dfsg-1build2`, prints `coqc --version`, and runs `make -C proofs`.

## Final verification

- `cargo fmt -- --check`
- `cargo clippy --all-targets -- -D warnings`
- `cargo test`
- `make -C proofs`
- `grep -R "Admitted\." -n proofs/theories` → 3 admitted theorem obligations

## Post-review ledger repair

A follow-up review found two ledger issues and both are repaired here:

- L6/L7 no longer appear as `Admitted` theorems concluding `True`. They are demoted in
  `Meta.v`, `proofs/README.md`, and this report to `Stated-Pending-Infrastructure` until
  the continuation resource model and instrumented frame-counting step relation exist.
- L8's admitted theorem now includes the missing true-solution hypothesis
  `(forall c', satisfies rho c')`, so the future solver proof does not inherit an
  obviously underconstrained `rho`.
