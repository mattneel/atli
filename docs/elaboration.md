# Surface-to-core elaboration (Sprint 05)

This document records the implemented subset mapping from `docs/syntax.md` to the reduced
core in `docs/calculus.md §10`.

- Top-level functions are elaborated into nested core `let` bindings ending in `main`'s
  body. Earlier declarations are available to later declarations; the core has no global
  namespace, so the file is closed by lexical `let` nesting.
- Surface functions with multiple parameters are curried: `f(a, b)` elaborates uniformly
  as `(f a) b`, matching `syntax.md §5`'s pipe rule and the unary core arrow.
- Recursive unary `Nat -> ...` functions elaborate to core `fix`; the boundedness slot
  chooses `Structural` (absent), `Measure` (`measure e`, parsed and conservatively
  accepted only when `e` is a Nat literal or parameter name), or `Div` (`div`) per
  `syntax.md §8`.
- Decimal Nat literals elaborate to unary `zero`/`succ` chains (`docs/calculus.md §3.2`).
- `case n { 0 -> e0 ; p -> e1 }` is the surface Nat eliminator: the second arm's name
  binds the predecessor, so it elaborates to `TCaseNat n e0 p e1`. This is the concrete
  Sprint 05 reading of `syntax.md §5` for the reduced core.
- Effect declarations are multi-label in Sprint 08: each `effect A { op(x: Nat) -> Nat }`
  interns a core label `A` (`docs/syntax.md §6`, `docs/calculus.md §2.2/§10`). The reduced
  operation name remains `op`; `A.op(e)` elaborates to `perform A e`.
- Handlers map directly to deep core handlers with a clause vector. `A.op(p), k -> k(v)`
  elaborates `k(v)` to core `resume`; `A.op(p), _ -> e` drops the continuation. A handler
  may carry clauses for several labels, and nested handlers over different labels are
  transparent to the operation search per `docs/calculus.md §5`. Mention-without-resume is
  intentionally allowed through parsing/elaboration and rejected by `check::check` under
  `docs/calculus.md §4.7`.
- Pipe desugaring follows `syntax.md §5`: `x |> f(a)` becomes `f(x, a)`, then currying
  maps that to `(f x) a`. Sprint 12 also threads pipes into prefix forms: `x |> inplace f(args)`
  elaborates as `inplace f(x, args)`, while `x |> freeze` and `x |> move` elaborate as
  `freeze x` and `move x`.
- Unsupported settled-but-out-of-reduced-core constructs (records, variants, `spawn`,
  `scope`, `if`, type parameters, strings/chars/floats, `use`/modules, and `^u`) diagnose
  as "not yet in the reduced surface" rather than silently elaborating. Multiple effect
  labels are no longer unsupported as of Sprint 08; `^`, arrays, `move`, `inplace`, and
  `freeze` are implemented as of Sprint 11.

## Arithmetic prelude (Sprint 06)

`+`, `-`, and `*` parse as left-associative binary operators with `*` binding tighter than
`+`/`-`, matching `docs/syntax.md §1`. They elaborate to injected library functions over
unary `Nat` only when used:

- `a + b` ⇒ `__atli_add(a, b)`
- `a - b` ⇒ `__atli_sub(a, b)`, with **monus** semantics: subtraction truncates at zero
  because reduced `Nat` has no negatives. Surface `Int` remains future work.
- `a * b` ⇒ `__atli_mul(a, b)`

The injected definitions are higher-order library recursion rather than core primitives.
Each closes over the first argument and uses a unary structural `fix` over the second
argument, which matches the current strict-descent checker. `sub` uses an injected private
`__atli_pred` helper; `mul` depends on `add`. Backends may recognize these injected
identities and lower them to native arithmetic as a performance decision, while the oracle
continues to run their unary core definitions.

## Tier-1 native recognition (Sprint 06)

`atli emit` / `atli build` consume the same elaboration but lower only the effect-free,
finite-β fragment. In that fragment, arithmetic prelude identities are treated as a
backend performance boundary: the oracle still sees unary library recursion, while the
tier-1 native harness lowers surface `+`, `-`, and `*` to native `i64` arithmetic. Monus
is emitted as `max(a - b, 0)`. This is semantics-preserving for the reduced `Nat` subset
and does not add primitive arithmetic to the core calculus.

## Real MLIR and handler lowering (Sprint 07)

Sprint 07 makes the MLIR module load-bearing: `atli build` lowers emitted MLIR through
`mlir-opt`/`mlir-translate` and links only a tiny runtime shim. The emission path never
calls the oracle interpreter; oracle execution is used only in tests to compare compiled
outputs after the fact.

Sprint 08 generalizes surface and core handlers to multiple labels. Sprint 09 adds the
compiled runtime handler-scope stack for dynamic search: entering a native `handle` pushes
label-keyed scope records carrying clause mode and handler-entry watermark, and `perform ℓ`
in called functions invokes `atli_scope_perform` to walk those records innermost-out per
`docs/calculus.md §5`. The drop/resume classification within a selected lexical clause
remains static and is still licensed by `L5_mentions_iff_resume`: dropped clauses compile
as `H-op-drop` and allocate no continuation frame, while resuming clauses compile as
`H-op-resume` and call a debug one-shot check before invoking the captured continuation
shape.

## Sprint 08 growable `Div` path

`β = ω` programs no longer fail at `atli build`. The emitter marks the MLIR module as
`atli.growable = true`, uses a growable initial segment size of 64 slots, and inserts a
test-harness tick in `div` functions. Setting `ATLI_MAX_ITERS=N` on the native executable
causes the runtime shim to exit successfully after `N` divergent iterations and report
`ATLI_GROWABLE_SEGMENT=64`; without that test variable the compiled program follows its
source divergence. Finite-β programs still use the exact certified arena and the same
overflow trap.

## Top-level declaration SCCs (Sprint 09)

Top-level function references are analyzed as a declaration call graph before lowering. Strongly
connected components with more than one function elaborate to `fix*` binding groups
(`docs/calculus.md §3/§4.8/§7.1`): every member is checked with all group members in scope, and each
surface name is bound to a projection of the shared group entry. Singleton declarations keep the
existing lowering: nonrecursive functions become lambdas, and self-recursive unary `Nat` functions
become unary `fix`.

The elaborator uses its own small Tarjan pass over surface declaration names rather than reusing the
boundedness solver's Tarjan; the two graphs have different domains. A cyclic group with the default
structural tag is intentionally rejected by the checker under the conservative §4.8 rule. Cyclic
surface groups should be annotated `measure n` or `div` until a future precision pass proves
cross-member structural descent.

## Arrays and affine uniqueness (Sprint 11)

`Array` is the monomorphic Nat-buffer surface type introduced by `docs/calculus.md §3/§9.2`.
`mkarray(n, v)` elaborates to core `mkarray`; `get(a, i)`, `set(a, i, v)`, and `len(a)`
elaborate to their corresponding core array terms. `set` is functional in the oracle and
allocates a copied array; `inplace set(a, i, v)` elaborates to core `inplace (set a i v)`
and is accepted only when the surface uniqueness pass has consumed a `^Array` handle for
`a`. The native backend lowers that accepted form to `atli_array_inplace_set`, a bare store
with no data-region allocation.

The surface `^T` marker is checked before core elaboration. Bindings of unique values are
affine (`Q = 1` per `docs/calculus.md §4.2`): `move`, `inplace`, passing to a unique
parameter, or using the value at shared type all consume the binding. Branches conservatively
join consumption, so a unique binding spent in either `case` arm is spent after the `case`.
`freeze e` is explicit-intent sugar for consuming subsumption from `^T` to `T`; it returns a
shared value that may be read without further uniqueness accounting.

The current surface has no local lambda syntax, so the tier-1 capture ban for unique outer
bindings is enforced at the core/rule level and documented as a future diagnostic expansion
when local closures land. Top-level unique parameters are not captures; they are ordinary
arguments and may be threaded through `^` parameters.
