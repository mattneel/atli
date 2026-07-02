# Atli Core Calculus (`λ_Atli`)

> **Status:** spike / draft 0.1. This is the *minimal core*, not the surface language.
> Its job is to be small enough to mechanize (Layer‑2 soundness target) and complete
> enough to drive the reference interpreter and the checker spike. The surface language
> elaborates *into* this core.

---

## 0. Purpose & scope

Atli is a **graded, coeffectful type theory with a systems backend**. A single kinded
*capability row* travels with every computation and records four proof obligations:

| Grade | What it tracks | Structure | Semantic payload |
|-------|----------------|-----------|------------------|
| `ε` (effects) | what a computation *does* | graded **monad**, join‑semilattice | which handlers must be in scope |
| `q` (uniqueness) | what a reference *consumes* | substructural semiring `{0,1,ω}` | in‑place & move licenses |
| `β` (boundedness) | the *frame size* a computation *demands* | graded **comonad**, quantitative (`ℕ ∪ {ω}`) | **the arena allocation size** |
| `ρ` (region) | *where* a frame/value lives | region lattice (spawn = arena = cancellation tree) | which arena to allocate in |

The load-bearing, genuinely-novel piece is the **interaction of `ε` and `β` at the
handler** (§6): effects propagate leaf→root, the boundedness that qualifies them
propagates root→leaf, and the two must reach a joint fixpoint. Everything else is
composition of known systems.

### What is settled prior art vs. what Atli owns

| Component | Prior art we stand on | Atli's delta |
|-----------|----------------------|--------------|
| Effect rows + row-polymorphic inference | Koka, Frank, Eff | — (reused) |
| Substructural / quantitative typing (`q`) | QTT (Atkey), Linear Haskell, Granule | — (reused) |
| Region/lifetime grade (`ρ`) | Tofte–Talpin, Cyclone, Verona | — (reused, lightened) |
| Totality via structural + well-founded recursion | Agda, Idris, Lean | applied *under native effects* |
| Effect × coeffect combination | Gaboardi et al., ICFP 2016; Granule | **quantitative β = arena size**; bespoke fixpoint solver; systems backend |
| Fixpoint + widening/narrowing | Cousot & Cousot (abstract interpretation) | **soundness criterion is inverted** (§7): the analysis *sizes an allocation*, so under-approximation corrupts memory |
| Frontend continuation splitting (no LLVM coroutines) | Zig (engineering precedent) | frames placed in arenas, sized by `β` |

---

## 1. Design axioms

1. **Legibility.** Every property the machine relies on is legible in the source and
   discharged by the type checker. A grade is not documentation; it is a *codegen
   license* — a proof obligation cashed at the backend to justify an
   otherwise-unsafe optimization.
2. **The ladder.** Every grade is a three-rung ladder: *default (free) → annotate
   (strengthen/weaken) → mark (escape)*. Same shape for memory (`hope`/`inplace`/
   `uniq`), uniqueness (`bare`/`^`/named), and termination
   (structural/measure/`div`). Learn the shape once.
3. **One-shot linearity is the keystone.** Continuations are affine (used ≤ 1). This
   single restriction makes four subsystems tractable at once — memory safety,
   frame-representation simplicity, totality-soundness-under-effects, and
   fixpoint decidability. It is non-negotiable: pulling it collapses all four.

---

## 2. Grade algebra

### 2.1 Uniqueness `q ∈ Q` — substructural semiring

```
Q = ({0, 1, ω}, +, ·, 0, 1)

    +  | 0 1 ω          ·  | 0 1 ω           order:  0 ≤ 1 ≤ ω
    ---+------          ---+------
    0  | 0 1 ω          0  | 0 0 0
    1  | 1 ω ω          1  | 0 1 ω
    ω  | ω ω ω          ω  | 0 ω ω
```

`0` = unused (permits weakening), `1` = unique/linear (exactly one reference),
`ω` = shared/unrestricted. Contexts are `Q`-graded vectors; the rules split and scale
contexts by pointwise `+` and `·` (QTT-style). Subtyping: `τ @ 1 <: τ @ ω`
(*forgetting* uniqueness is always safe; recovering it never is).

### 2.2 Effects `ε ∈ Eff` — graded monad

```
Eff = (𝒫(Label), ∪, ∅)          order: ε₁ ⊑ ε₂  ⟺  ε₁ ⊆ ε₂
```

Join-semilattice. Sequential composition = `∪`. `Label` is now an open finite set of
operation labels `ℓ₁ … ℓₙ`; Sprint 01's single `ℓ` was the reduced target, not a different
algebra. **Covariant** subsumption in the grade: `T ! ε` coerces to `T ! ε'` when
`ε ⊑ ε'` (a less-effectful computation is usable as a more-effectful one). For
principality, *minimize* `ε`.

### 2.3 Boundedness `β ∈ Bound` — graded comonad, quantitative

```
Bound = (ℕ ∪ {ω}, ⊕, ⊔, 0)

  ⊕  (sequential frame nesting)   =  saturating addition:  a ⊕ b = a + b,   ω ⊕ _ = ω
  ⊔  (branch join)                =  max:                  a ⊔ b = max(a,b), ω ⊔ _ = ω
  identity for both               =  0
  order                           =  ≤  on  ℕ ∪ {ω},   with  n < ω  for all n ∈ ℕ
```

`β` is the number of bytes the computation's continuation frame demands. `ω` = "not
statically bounded → grows a stack." The grade is **comonadic**: it sits in
*contravariant* position under the arrow (it is a demand on context, not a product of
the computation). See §7 for how recursion induces a fixpoint over `Bound`.

> **The inverted soundness direction (read this twice).** In classical abstract
> interpretation, over-approximating a bound *up* is always sound because the analysis
> proves a *safety* property. Here `β` **is the allocation size**. Therefore:
> - too *small* ⟹ under-allocation ⟹ **frame overflows its arena ⟹ memory corruption**;
> - too *large* ⟹ merely wasted bytes.
>
> Over-approximation (widening jumps *up*) is the *safe* direction — good. But the
> least fixpoint is computed by iterating *up from 0*, so **every pre-convergence
> iterate is an under-estimate**. A partial iterate reaching codegen is a miscompile.
> This is why §7 mandates a phase gate: grades are write-only until their SCC's
> fixpoint is certified converged.

### 2.4 Regions `ρ ∈ Region` — region lattice

`Region` is a lattice of arena identifiers ordered by outlives: `ρ_child ⊑ ρ_parent`
(a child arena is nested in, and outlived by, its parent). Structure mirrors the
spawn/cancellation tree: **spawn = arena = cancellation** is one tree, and `Region` is
its order. A value in an outer (longer-lived) region may be used where an inner region
is expected. (Treated lightly in the core; the metatheory here is standard
region-calculus and not where the novelty lives.)

### 2.5 The capability row

```
σ  =  ⟨ ε ; β ; ρ ⟩
```

Row subsumption `σ ⊑ σ'` is **not** a uniform product order — the components have
different variance under the arrow (§4, rule `Sub` and `→`-subtyping). This variance
mismatch is the technical heart of the principality obligation (§8.6).

---

## 3. Syntax

### 3.1 Types

```
value type      τ ::= Unit | Bool | Nat | Array[T]
                    | (T →[σ] T)               function; latent row σ fires on apply
                    | ⟨ ℓ:T, … ⟩               record
                    | [ ℓ:T | … ]              variant
                    | Task                     opaque task handle (surface-only)
                    | Cont[σ] T T              one-shot continuation (resume-type, answer-type)
                    | μα. τ  |  α              (structurally-bounded) recursive type

graded type     T ::= τ @ q                    value type with uniqueness grade q ∈ Q
poly type       ∀A⃗. T                    rank-1 declaration/function polymorphism

computation     C ::= T ! σ                    produces T, runs with capability row σ
```

`Cont[σ] A R` is the type of a captured continuation: given a resume value of type `A`
it yields the answer `R`, running with row `σ`. It is **always** introduced at
uniqueness `1` (affine) — see `Handle`.

### 3.2 Terms

```
e ::= x
    | () | true | false
    | zero | succ e                    unary naturals
    | case e { zero => e₀ ; succ x => e₁ }
                                       Nat eliminator; x is the predecessor subterm
    | mkarray(e_len, e_fill)           Nat array, length e_len, filled with e_fill
    | get(e_arr, e_idx)                read Nat from array
    | set(e_arr, e_idx, e_val)         functional update: copy array, then write
    | len(e_arr)                       array length as Nat
    | λ x:T. e                        abstraction
    | e₁ e₂                           application
    | let x = e₁ in e₂                sequencing (monadic bind)
    | fix f:(T →[σ] T). λ x. e         recursion  (induces the β-constraint, §7)
    | fix* { fᵢ:(Tᵢ →[σᵢ] Uᵢ) = λ xᵢ. eᵢ }ᵢ  mutual recursive binding group
    | ⟨ ℓ = e, … ⟩ | e.ℓ              record intro / proj
    | ⟨ e | ℓ = e' ⟩                  functional record update: shallow-copy, replace ℓ
    | C(e₁, …, eₙ)                    nominal variant constructor application
    | case e { Cᵢ(p⃗ᵢ) => eᵢ ; … ; _ => e? }
                                       variant/record eliminator with exhaustive patterns
    | perform ℓᵢ e                    invoke effect operation ℓᵢ
    | handle e with H                 effect handler (deep)
    | resume k e                      invoke a captured continuation (consumes k)
    | move e                          transfer unique ownership (consumes e)
    | inplace e                       destructive update; operand is a set(...)
    | freeze e                        explicit unique-to-shared coercion sugar
    | scope { e }                     structured task group and region
    | spawn f(e₁, …, eₙ)              start top-level function f in nearest scope
    | await e                         consume a task handle and produce its result

H ::= { return x → e_ret ; (ℓᵢ pᵢ kᵢ → eᵢ)ᵢ∈I }
```

Handler `H` has one return clause and a finite clause set over handled labels
`dom(H) = {ℓᵢ | i ∈ I}`. In clause `ℓᵢ pᵢ kᵢ → eᵢ`, `pᵢ` binds the operation argument and
`kᵢ : Cont[…] Aᵢ R @ 1` names the **one-shot** delimited continuation up to the enclosing
`handle` for that label. The continuation is materialized lazily: a clause that does not
use its own `kᵢ` does not allocate or carry the delimited frame.


**Nominal aggregate declarations and type parameters.** Records and variants may be
monomorphic or rank-1 parametric declarations: `type Point = { x: Nat, y: Nat }`,
`type Option[A] = None | Some(A)`, `type List[A] = Nil | Cons(A, List[A])`, and
`type Pair[A, B] = { fst: A, snd: B }`. Type parameters are declared in brackets and are
in scope only in that declaration. Type application arity is checked (`Option[Nat, Nat]`
is an error) and unbound type variables are errors. Recursive declarations are allowed
only through variants: `type List[A] = Nil | Cons(A, List[A])` is valid, while a pure
record cycle is rejected by the occurs-check because it has no base constructor.

**Generic functions.** Functions may quantify type parameters in the same rank-1 style:
`fn map[A, B](...)`. The body checks once, polymorphically, with no constraints, traits,
or bounded polymorphism. Call sites instantiate parameters by unifying declared argument
types with actual argument types; an instantiation failure blames the parameter, the
conflicting types, and both argument sites. Generic higher-order functions in tier 1 take
pure function arguments only: effect-row variables and open rows remain out of scope.

**Generic arrays and tasks.** `Array[A]` generalizes the former Nat-only array; bare
`Array` is a deprecated alias for `Array[Nat]`. `Task[T]` may be written in surface
signatures, but task handles remain opaque, affine, scope-local values with the same
structured-concurrency restrictions as before.

**Tasks and scopes.** `scope { e }` owns a task group and a region. Every `spawn` inside
attaches to the nearest enclosing scope, and scope exit joins all children before freeing
the scope region wholesale. `spawn f(v⃗)` requires `f` to be a declared top-level function:
there is no closure capture in this tier. Arguments are evaluated at the spawn site in the
parent, and grade consumption for those arguments happens there; `spawn process(move m)` is
the idiomatic ownership-transfer point. `spawn` yields an opaque task handle, and `await h`
consumes that handle and yields the task's result. Task handles bind to locals only, may not
be stored in arrays or aggregates, may not escape their scope by return, and may not be
passed to `spawn`.

---

## 4. Typing

Judgment:

```
Γ ⊢ e : T ! σ
```

"Under `Q`-graded context `Γ`, term `e` produces value type `T` and runs with
capability row `σ = ⟨ε; β; ρ⟩`." Context operations `Γ₁ + Γ₂` (pointwise `+` in `Q`)
and `q · Γ` (pointwise `·`) manage substructural usage. `0 · Γ` denotes `Γ` with all
grades zeroed (weakenable).

Notation: `σ₁ ▷ σ₂` = sequential row composition = `⟨ ε₁ ∪ ε₂ ; β₁ ⊕ β₂ ; ρ₁ ⊓ ρ₂ ⟩`.
`σ₁ ⊔ σ₂` = branch join = `⟨ ε₁ ∪ ε₂ ; β₁ ⊔ β₂ ; ρ₁ ⊓ ρ₂ ⟩`.
The **pure** row is `ø = ⟨ ∅ ; 0 ; ρ_top ⟩`.

### 4.1 Structural rules

```
────────────────────────  (Var)
x :[1] T , 0·Γ  ⊢  x : T ! ø


Γ ⊢ e : T ! σ        q' ⊑ q
──────────────────────────────  (Weaken-Uniq)     -- forget uniqueness
Γ ⊢ e : (τ @ q') ! σ            where T = τ @ q
```

Bare surface types elaborate to unrestricted grade `ω`; this sprint keeps the
implemented reading that bare means shared, rather than retroactively making every
existing signature uniqueness-polymorphic. A `^T` binding elaborates to `T @ 1` and is
**affine**: it may be used at most once, and zero uses are legal. A use of a `1`-graded
binding is any of:

- passing it to a `^`-typed parameter;
- using it as the operand of `move`;
- using it as the target array of `inplace set(...)`;
- using it at shared type through `Weaken-Uniq` / subsumption.

Forgetting uniqueness consumes the binding. This is load-bearing: if a unique handle
survived a shared use, `f(a); inplace set(a, i, v)` could mutate under `f`'s live alias.
To keep a shared value around, bind the forgotten result: `s = freeze a`; `s` has grade
`ω` and can be used freely.

Branches are alternatives, so consumption joins conservatively: if a `1`-graded binding
is consumed in either arm of a `case`, it is spent after the whole `case`. Tier-1
closures are also conservative: a `1`-graded binding may not be captured by `λ`, `fix`,
or `fix*` bodies because those bodies can run zero or many times. The required
diagnostic is: "unique binding `a` captured by function; pass it as a `^` parameter
instead." Threading ownership through `^` parameters is the sound idiom; relaxing this
for once-called closures is a future precision extension.

**Uniqueness-preservation variables (`^u`).** A signature position `^u A` implicitly
binds the lowercase uniqueness variable `u` for that signature. At a call site, a unique
argument instantiates `u := 1`; a shared argument instantiates `u := ω`; every result or
argument position annotated with the same `^u` uses that instantiated grade. Thus
`fn through[A](x: ^u A) -> ^u A = x` preserves whatever grade the caller supplied.

The load-bearing rule: `^u` grants threading, never privileges. Because the body checks
once and must be sound at both `u = 1` and `u = ω`, a `^u` value inside the body is
affine and may flow to another `^u` position, be returned at `^u`, or be forgotten, but it
may **not** be the target of `inplace` or the operand of `move`; those require a definite
`1`. Otherwise the `u = ω` instantiation would mutate through aliases retained by the
caller. The required diagnostic is: "`x` is `^u`: uniqueness-preserving parameters grant
threading, not mutation; take `^A` if this function must mutate." The combinator-doubling
problem solved by the original design's Reading B is handled explicitly by `^u`; revisiting
bare-parameter polymorphism is a future compatibility decision, not a silent migration.

Generic payload grading is conservative. Destructuring a unique aggregate whose payload
has type parameter `A` binds the payload at grade `1` because `A` may instantiate to a
heap type; if `A = Nat` this is stricter than necessary but sound. Copy-field peek on an
`A`-typed field of a unique record is rejected with the same destructure-or-freeze
suggestion used for heap fields. A heap-ness-aware refinement is future work.

### 4.2 Naturals

Unary natural introduction and elimination make structural descent explicit: in the
`succ x` branch, `x` is a strict subterm of the scrutinee.

```
──────────────────────────────  (Zero)
Γ ⊢ zero : Nat @ 1 ! ø

Γ ⊢ e : Nat @ q ! σ
──────────────────────────────  (Succ)
Γ ⊢ succ e : Nat @ 1 ! σ

Γ₀ ⊢ e : Nat @ q ! σ       Γ₁ ⊢ e₀ : T ! σ₀
Γ₂ , x :[q_x] Nat @ 1 ⊢ e₁ : T ! σ₁
────────────────────────────────────────────────────────────  (Case-Nat)
Γ₀ + Γ₁ + Γ₂ ⊢ case e { zero => e₀ ; succ x => e₁ }
  : T ! σ ▷ (σ₀ ⊔ σ₁)
```

If the case scrutinee is the parameter of an enclosing structural `fix`, recursive calls
on the `x` bound by the `succ x` branch satisfy the strict-descent side condition in
`Fix` (§4.8): each recursive step peels exactly one `succ`.

### 4.3 Functions

Abstraction records the body's row as the arrow's *latent* row:

```
Γ , x :[q] T₁  ⊢  e : T₂ ! σ
────────────────────────────────────  (Abs)
Γ  ⊢  λx:T₁. e  :  (T₁ →[σ] T₂) @ 1  !  ø
```

Application fires the latent row and composes it with the rows of evaluating the
function and argument. Note `β` **adds** (`⊕`): the callee's frame nests inside the
caller's.

```
Γ₁ ⊢ e₁ : (T₁ →[σ_f] T₂) @ q  ! σ₁
Γ₂ ⊢ e₂ : T₁ ! σ₂
──────────────────────────────────────────────  (App)
Γ₁ + Γ₂  ⊢  e₁ e₂  :  T₂  !  σ₁ ▷ σ₂ ▷ σ_f
```

### 4.4 Sequencing (bind)

```
Γ₁ ⊢ e₁ : T₁ ! σ₁          Γ₂ , x :[q] T₁ ⊢ e₂ : T₂ ! σ₂
──────────────────────────────────────────────────────────  (Let)
Γ₁ + Γ₂  ⊢  let x = e₁ in e₂  :  T₂  !  σ₁ ▷ σ₂
```

### 4.5 Uniqueness escapes

```
Γ ⊢ e : (τ @ 1) ! σ                       Γ ⊢ e : (τ @ 1) ! σ
──────────────────────────  (Move)        ──────────────────────────  (Inplace)
Γ ⊢ move e : (τ @ 1) ! σ                  Γ ⊢ inplace e : (τ @ 1) ! σ

Γ ⊢ e : (τ @ 1) ! σ
──────────────────────────  (Freeze)
Γ ⊢ freeze e : (τ @ ω) ! σ
```

Both *require* `q = 1` in the premise. `move` re-issues a unique reference to a fresh
region (enabling zero-copy cross-task transfer, checked against `ρ`); `inplace`
licenses destructive mutation in the backend (§9). Neither is well-typed on a `ω`
(shared) value — that is a compile error naming the alias that forced sharing.
`freeze` is explicit-intent surface sugar for the same unique-to-shared coercion as
`Weaken-Uniq`; it consumes the unique binding and returns a shared value.

### 4.5.1 Arrays

`Array[A]` is parametric in its element type; bare `Array` is an alias for `Array[Nat]`. The array handle itself has a uniqueness
grade; elements are stored in one uniform slot, and element values follow the ordinary grade rules.

```
Γ₁ ⊢ n : Nat @ q₁ ! σ₁       Γ₂ ⊢ v : A @ q₂ ! σ₂
────────────────────────────────────────────────────  (MkArray)
Γ₁ + Γ₂ ⊢ mkarray(n, v) : Array[A] @ 1 ! σ₁ ▷ σ₂

Γ₁ ⊢ a : Array[A] @ q ! σ₁      Γ₂ ⊢ i : Nat @ qᵢ ! σ₂
────────────────────────────────────────────────────  (Array-Get)
Γ₁ + Γ₂ ⊢ get(a, i) : A @ ω ! σ₁ ▷ σ₂

Γ₁ ⊢ a : Array[A] @ q ! σ₁      Γ₂ ⊢ i : Nat @ qᵢ ! σ₂      Γ₃ ⊢ v : A @ qᵥ ! σ₃
───────────────────────────────────────────────────────────────────────────────  (Array-Set)
Γ₁ + Γ₂ + Γ₃ ⊢ set(a, i, v) : Array[A] @ 1 ! σ₁ ▷ σ₂ ▷ σ₃

Γ ⊢ a : Array[A] @ q ! σ
────────────────────────────  (Array-Len)
Γ ⊢ len(a) : Nat @ ω ! σ
```

`set` is functional: it allocates a fresh array, copies `a`, writes index `i`, and yields
the fresh unique handle. `inplace set(a, i, v)` is the destructive specialization of
`Array-Set`: it is well-typed only when the target `a` is consumed at grade `1`, and it
yields the same unique handle after mutation. Out-of-bounds `get`/`set` is defined
behavior: the oracle reaches a bounds-error outcome and compiled code traps with exit 88
and message `ATLI BOUNDS`.


### 4.5.2 Records, variants, and aggregate uniqueness

Aggregate construction is **born unique**: a record literal or variant constructor yields
`^T` (`T @ 1`) and may be immediately forgotten by subsumption. If an initializer is
itself `1`-graded, construction consumes it: ownership moves into the aggregate.

Projection distinguishes copied scalars from heap aliases. Projecting a `Nat` or `Unit`
field from a unique record is a non-consuming read because it copies an unboxed value.
Projecting a heap-typed field (`Array`, record, or variant) from a unique record is a type
error: freeze the record to share it, or destructure it to take ownership. Projection from
a shared record is unrestricted at every field type.

Tier 1 has **no path-inplace**. `inplace set(r.buf, i, v)` is rejected because it would
borrow through a path. The licensed record mutation is in-place field replacement:
`inplace ⟨ r | ℓ = e ⟩` on a unique record consumes `r`, stores the new field handle/value,
and yields the same unique record. Functional update `⟨ r | ℓ = e ⟩` shallow-copies the
record and replaces `ℓ`.

**Destructure-consume.** A `case` over a unique aggregate consumes the aggregate handle.
Pattern bindings inherit grade by payload type: heap-typed fields/payloads bind at `1`
(unique ownership transferred out of the dead aggregate), while `Nat` and `Unit` bind at
`ω`. A `case` over a shared aggregate consumes nothing and binds every payload at `ω`.
This is sound because the aggregate handle is dead after the match; it is the aggregate
analogue of `move` and is the way a unique buffer leaves a unique message record.

Variant cases must be exhaustive over the declared constructors unless they include `_`;
non-exhaustive cases are checker errors listing the missing constructors. Constructor
pattern payloads are also the strict subterms used by structural recursion (§4.8/§7): a
recursive call at the free rung may pass a payload bound by a constructor or record pattern
of the current parameter's scrutinee.

### 4.5.3 Tasks

Task handles are affine: `await h` consumes `h`, and a second `await` is the same
two-location use-after-consume error as `move` or `inplace`. Dropping a handle is legal
because `scope` joins outstanding children at exit and discards their results.

```
Γ ⊢ e : T ! σ
──────────────────────────  (Scope)
Γ ⊢ scope { e } : T ! σ

f : (T₁ → … → Tₙ →[σ_f] U)      ε_f = ∅
Γᵢ ⊢ eᵢ : Tᵢ ! σᵢ
────────────────────────────────────────────  (Spawn)
Σᵢ Γᵢ ⊢ spawn f(e₁,…,eₙ) : Task[U] @ 1 ! (▷ᵢ σᵢ)

Γ ⊢ h : Task[U] @ 1 ! σ
──────────────────────────  (Await)
Γ ⊢ await h : U ! σ
```

`Task[U]` is internal checker notation; the surface type is the opaque `Task`. `spawn`
requires the callee row to be effect-closed (`ε_f = ∅`): a spawned task must handle its
own effects. Cross-task handler inheritance would require continuations spanning a child
stack and is future research, not an implicit tier-1 feature. `Div` callees are spawnable;
their handles obey the same affine await/drop rule, while bounded test runs use §5's
budget outcome. Unique arguments are consumed at the spawn site exactly as ordinary
arguments are, so passing one `^` value to two spawns is the standard double-use error
blamed across both spawn sites. Task handles are scope-local and may not be stored in data
structures, returned, or passed to another task.

### 4.6 Effects

```
Γ ⊢ e : A ! σ            (ℓ : A ↠ B) ∈ Signature
─────────────────────────────────────────────────  (Perform)
Γ ⊢ perform ℓ e : B  !  σ ▷ ⟨ {ℓ} ; β_ℓ ; ρ ⟩
```

`perform ℓ` adds `ℓ` to the effect grade and contributes the operation's own frame
cost `β_ℓ`. The operation's resume-type `B` is what a handler's continuation will be
fed. Nothing here says whether `ℓ` terminates — that is decided *at its handler*.
Likewise, the continuation variable is not available at the `perform` site; the
mention-implies-resume discipline for handler-bound `k` is imposed by `Handle` (§4.7).

### 4.7 The handler rule — the centerpiece

*(Deep handlers: the continuation reinstalls `H`. See §6 for the full discussion, and
§6.2 for the one-shot lemma that makes the `β`-side sound.)*

Let `H = { return x → e_r ; (ℓᵢ pᵢ kᵢ → eᵢ)_{i∈I} }` handle operation set
`L = {ℓᵢ}_{i∈I}`.

```
(handled body)
Γ_b ⊢ e : T ! ⟨ ε ; β ; ρ ⟩            L ⊆ ε

(return clause)
Γ_r , x :[q_r] T ⊢ e_r : R ! σ_r

(for each i ∈ I, with resume-type Bᵢ of ℓᵢ and argument-type Aᵢ)
Γᵢ , pᵢ :[q_p] Aᵢ , kᵢ :[1] (Cont[σ_kᵢ] Bᵢ R)  ⊢  eᵢ : R ! σᵢ
        where  σ_kᵢ  =  ⟨ ε \ L ; β ; ρ ⟩          -- k carries the *body's* frame β
        and    kᵢ ∉ FV(eᵢ)
              or eᵢ contains exactly one occurrence of resume kᵢ v
                 and no other free occurrence of kᵢ
──────────────────────────────────────────────────────────────────────────  (Handle)
Γ_b + Γ_r + Σᵢ Γᵢ
   ⊢  handle e with H
   :  R  !  ⟨ (ε \ L) ∪ ε_r ∪ (⋃ᵢ εᵢ)
            ;  β_setup ⊕ ( β_r ⊔ ⊔ᵢ β̂ᵢ )
            ;  ρ ⟩
```

The final side condition is the reduced core's continuation-use discipline: mentioning
`kᵢ` is relevant, and a relevant `kᵢ` must be consumed by exactly one direct `resume`.
A clause such as `let z = kᵢ in e` is not well-typed. This makes the syntactic
lazy-capture dispatch in §5 complete for typed programs.

where each clause's *effective* boundedness `β̂ᵢ` accounts for lazy continuation
materialization:

```
β̂ᵢ  =  βᵢ                     if eᵢ does not use/resume kᵢ      (lazy drop; no frame capture)
β̂ᵢ  =  βᵢ ⊕ β                 if eᵢ resumes kᵢ exactly once     (β = captured body frame)
```

There is deliberately **no** `βᵢ ⊕ (n · β)` case: `kᵢ` is typed `[1]`, so it resumes
at most once, so the continuation's frame enters **additively, never multiplicatively**.
There is also no implicit `β` charge for dropped clauses: because capture is lazy,
exception/default handlers are frame-free unless they actually resume. This is the whole
trick (§6.2).

Key facts encoded above:
- **Effect discharge:** `L` is removed from the result effect (`ε \ L`); the handler's
  own effects (`ε_r`, `εᵢ`) are added back.
- **`k` is affine, relevant when mentioned, and lazy:** grade `1`; the type system
  permits `0` uses only when `k` is absent from the clause. If `k` appears free, that
  occurrence must be exactly one `resume k v`. A `0`-use clause does not capture the
  continuation frame. It **cannot** be `ω`.
- **Boundedness co-propagation:** `k`'s row `σ_kᵢ` carries the *body's* `β` *inward* to
  the clause. If `eᵢ` resumes, that `β` is paid; the handler's own `β` then flows back
  *outward* in the result row. Effects out, boundedness qualifier in, at the same site.

### 4.8 Recursion

```
Γ , f :[ω] (T₁ →[σ] T₂) , x :[q] T₁  ⊢  e : T₂ ! σ'
      σ = ⟨ ε ; β ; ρ ⟩ ,  σ' = ⟨ ε' ; β' ; ρ' ⟩
      side condition:   ε' ⊑ ε ,   ρ' ⊑ ρ ,   β  ⊒  Fix_β(f, e)     -- see §7
──────────────────────────────────────────────────────────────────────  (Fix)
Γ ⊢ fix f. λx. e : (T₁ →[σ] T₂) @ 1 ! ø
```

The occurrences of `f` in `e` make `β` **recursive**: `β` must satisfy
`β ⊒ Fix_β(f, e)`, whose least solution over `Bound` is computed in §7. A mutual group
checks every body with all `fᵢ` in scope and emits one unknown `βᵢ` per member. Tags are
per member. The reduced structural rule is conservative: a `Structural` member may not
participate in an inter-member cycle; cyclic groups use `measure` or `div`. Future
precision may prove descent around an entire call cycle, but Sprint 08 chooses the
minimal sound rule.

For the structural/free rung, the concrete strict-descent condition is: a recursive call
may use only a variable bound by a `succ x` pattern whose scrutinee is the current
recursive parameter. That variable is a strict subterm of the scrutinee because the `case`
rule has peeled one `succ`. If the resulting lfp is finite, the frame is statically sized
(stackless codegen); if it widens to `ω`, the function is `div` and gets the stackful
fallback.

### 4.9 Subsumption (mind the variance)

```
Γ ⊢ e : T ! σ        T <: T'        σ ⊑⁺ σ'
─────────────────────────────────────────────  (Sub)
Γ ⊢ e : T' ! σ'
```

Row subsumption `σ ⊑⁺ σ'` at the **top level of a computation** is monotone in every
component: `ε ⊆ ε'` (may add effects), `β ≤ β'` (may claim a **larger** frame — the
*safe* direction, §2.3), `ρ' ⊑ ρ` (may narrow the region).

Function subtyping is where the comonadic contravariance appears:

```
T₁' <: T₁        T₂ <: T₂'        σ ⊑⁺ σ'
        ── AND the argument's demanded frame is contravariant ──
        β(T₁' as captured) ⊇ β(T₁ as captured)
──────────────────────────────────────────────────  (Sub-→)
(T₁ →[σ] T₂) <: (T₁' →[σ'] T₂')
```

> The `β` demand on a function's *argument/environment* varies **opposite** to the
> `β` on its *result row*. That mismatch — covariant effect grade meeting
> contravariant boundedness grade at the arrow — is exactly the obligation in §8.6.
> The rules above are the intended *declarative* system; the algorithmic solver (§7)
> must be proven to infer principal types with respect to it.

---

## 5. Operational semantics

Small-step, call-by-value, over evaluation contexts. `E` ranges over *handler-free*
evaluation contexts (no `handle` frame between the hole and the redex); `H`-delimited
context is handled explicitly by the two handler rules.

```
E ::= [·] | succ E | case E { zero => e₀ ; succ x => e₁ }
    | E e | v E | let x = E in e | perform ℓ E | E.ℓ | resume E e | resume v E
    | mkarray(E, e) | mkarray(v, E) | get(E, e) | get(v, E)
    | set(E, e, e) | set(v, E, e) | set(v, v, E) | len(E)
    | ⟨…, ℓ = E, …⟩ | E.ℓ | ⟨E | ℓ = e⟩ | ⟨v | ℓ = E⟩ | C(v⃗, E, e⃗)
    | move E | inplace E | freeze E
    | scope { E } | spawn f(v⃗, E, e⃗) | await E
```

Core reductions:

```
(λx. e) v                      →   e[x := v]                              (β)
let x = v in e                 →   e[x := v]                              (let)
case zero { zero => e₀ ; succ x => e₁ }
                                  →   e₀                                  (case-zero)
case (succ v) { zero => e₀ ; succ x => e₁ }
                                  →   e₁[x := v]                          (case-succ)
fix f. λx. e                   →   λx. e[f := fix f. λx. e]               (unfold)
⟨…, ℓ = v, …⟩.ℓ                →   v                                     (proj)
⟨R | ℓ = v⟩                    →   R'                                   (record-update)
     where R' is a shallow copy of R with field ℓ replaced.
inplace ⟨R | ℓ = v⟩            →   R                                    (record-inplace)
     mutating R.ℓ := v in place.
case Cⱼ(v⃗) { …; Cⱼ(x⃗) => eⱼ; … } → eⱼ[x⃗ := v⃗]                       (case-ctor)
case R { ⟨ℓᵢ = xᵢ⟩ => e }       →   e[xᵢ := R.ℓᵢ]                       (case-record)
mkarray(n, v)                  →   A                                    (array-new)
     where n is a Nat value and A is a fresh length-n heap array filled with v.
get(A, i)                      →   A[i]                                  (array-get)
set(A, i, v)                   →   A'                                   (array-set)
     where A' is a fresh copy of A with A'[i] = v.
inplace set(A, i, v)           →   A                                    (array-inplace)
     mutating A[i] := v in place.
len(A)                         →   |A|                                  (array-len)
move v                         →   v                                    (move)
freeze v                       →   v                                    (freeze)
spawn f(v⃗)                    →   h                                    (spawn-oracle)
     where the oracle evaluates f(v⃗) to completion immediately and stores its outcome in h.
await h                        →   v                                    (await-oracle)
     when h stores value v; an exhausted divergent child stores the budget outcome.
scope { v }                    →   v                                    (scope-return)
     after every child attached to the scope has joined.
```

Out-of-bounds `array-get`, `array-set`, and `array-inplace` step to a distinguished
bounds-error outcome. The oracle may implement `array-inplace` by the same always-copy
semantics as `array-set`; the observable contract is that, under §4's affine discipline,
`inplace set(A, i, v)` and `set(A, i, v)` are observationally equivalent because the
mutated array has no other live reference. Native code is allowed to cash the `q = 1`
license by mutating in place; the reference interpreter remains the always-copy oracle.

Handler reductions (deep):

```
handle v with H                →   e_r[x := v]                           (H-return)

handle E[perform ℓ v] with H   →   e_ℓ[ p := v ]                         (H-op-drop)
     when  ℓ ∈ dom(H), E is handler-free for ℓ, and k ∉ FV(e_ℓ).
     No continuation is materialized; the captured frame is not allocated.

handle E[perform ℓ v] with H   →   e_ℓ[ p := v ,
                                        k := κ ]                         (H-op-resume)
     when  ℓ ∈ dom(H), E is handler-free for ℓ, and k ∈ FV(e_ℓ), where
     κ  =  λ y. handle E[y] with H          -- deep: H reinstalled
     and κ is marked ONE-SHOT.

`E` is handler-free for `ℓ` when its hole is not underneath a nested handler whose
`dom(H')` contains `ℓ`. A nested handler for a different label `ℓ' ≠ ℓ` is transparent to
this search. Thus `perform ℓ` is captured by the innermost dynamically enclosing handler
that has a clause for `ℓ`, not merely by the nearest syntactic handler of any label.

resume κ v                      →   κ v            if κ not yet used      (resume)
resume κ v                      →   ⊥ (stuck)      if κ already used      (one-shot violation)
```

The one-shot marking on materialized `κ` is the operational witness of the `[1]` grade in
`Handle`; dropped clauses have no `κ` to mark because lazy capture avoids allocation.
Preservation (§8.2) guarantees the stuck case is unreachable in well-typed programs;
it is retained so the reference interpreter can *detect* a violation during testing
(Layer‑1 property: "no well-typed program reaches `resume`-after-use").

**Sequential oracle for tasks.** The reference oracle is deterministic: `spawn f(v⃗)` runs
`f(v⃗)` to completion immediately in depth-first order and records the result in the task
handle; `await` reads and consumes that result; scope exit has no remaining work because all
children are already complete. Under an `ATLI_MAX_ITERS`-style budget, a `Div` child that
exhausts its budget stores the exhaustion outcome, and joining/awaiting it reports that
outcome consistently with the top-level divergent oracle path.

**L10 schedule-independence claim.** For well-typed programs, every fair interleaving of
native task steps yields the same observable final value and per-task trap outcomes as the
sequential oracle. Sketch: mutation requires a `^` handle; `^` handles are affine; spawn
arguments are consumed at the spawn site; task handles cannot leak or be duplicated; therefore
no mutable heap object is reachable from two simultaneously running tasks. The race falsifier
for this claim is the ill-typed program that hands one array handle to two spawned tasks and
mutates through both handles.

---

## 6. The handler rule, in depth

### 6.1 Why this is the only novel rule

Away from handlers, effects propagate as effects (Koka-style row inference — settled)
and boundedness propagates as boundedness (Agda/Idris totality — settled). The **only**
site where the graded monad `ε` and the graded comonad `β` *interact* is `Handle`:
discharging an effect requires reasoning about the continuation `k`, and `k`'s frame is
the body's `β` carried *inward*. Concentrating the novelty in one rule is deliberate —
it means the Layer‑2 proof (§10) targets a calculus with **one effect and one handler**,
small enough to mechanize, and everything else is inherited soundness by composition.

This rule is the **`⟨⟩`-combining operator of Gaboardi et al. (2016)** specialized to
`Eff × Bound` with a quantitative comonad and an affine continuation.

### 6.2 The one-shot lemma (the load-bearing fact)

> **Lemma (affine continuations bound the boundedness fixpoint).**
> If every continuation `k` introduced by `Handle` has uniqueness grade `1`, then the
> boundedness contribution of any operation clause is *additive* in the body frame `β`
> when the clause resumes, and zero in the body frame when the clause drops:
> `β̂ᵢ ∈ { βᵢ , βᵢ ⊕ β }`. For well-typed clauses,
> `kᵢ ∈ FV(eᵢ) ⇔ eᵢ` contains exactly one direct `resume kᵢ v`; this lemma licenses the
> operational FV-dispatch in §5. Consequently the recursive `β`-constraint induced by a
> handled loop is of the form `β ⊒ c ⊕ β_rec` (additive), whose lfp over `Bound` is
> finite whenever the recursion depth is finite.
>
> *Contrapositive (why multi-shot is banned):* a multi-shot `k` (grade `ω`) invoked `n`
> times contributes `n · β`. With `n` unbounded, the constraint becomes
> `β ⊒ c ⊕ (ω · β)`, whose lfp is `ω` for any `c > 0` — every handled loop would be
> `div`, and the quantitative grade would carry no information. One-shot linearity is
> precisely what keeps `β` finite and therefore *informative*.

This is the same `[1]` grade that gives memory safety (no aliasing a resumed frame) and
frame-representation simplicity (frames are consumed-once, no re-entrant machinery). One
restriction, four payoffs.

### 6.3 Shallow vs deep

The core uses **deep** handlers (`κ` reinstalls `H`), which compose better and match the
intended surface semantics. A shallow variant (`κ` does *not* reinstall `H`) is a
straightforward alternative rule; it changes `σ_kᵢ` to drop the outer handler and is
noted here only as a known design point, not adopted.

---

## 7. Boundedness: fixpoint, widening, phase discipline

### 7.1 Constraint generation

`Fix`, `App`, `Let`, and `case` generate a system of constraints over `Bound`-valued
unknowns (one per definition, plus row variables). All constraints have the monotone
shape `βₓ ⊒ Φₓ(β⃗)` where `Φ` is built from `⊕` (nesting), `⊔` (branching), and
substitution at recursive occurrences. Binding groups generate mutually-referential
constraints: a cyclic group naturally produces a multi-node SCC over the `βᵢ` unknowns of
its members, giving §7.2's SCC solver its source in the core language rather than only in
hand-built tests. For structural recursion over `Nat`, a recursive occurrence is accepted
at the free rung only when its argument is the predecessor variable introduced by a
surrounding `succ x` branch for the current recursive parameter. The intended solution is
the **least fixpoint** `lfp Φ` (tightest sound frame sizes).

### 7.2 Solving

1. **SCC decomposition.** Build the call/definition graph; compute strongly-connected
   components. Solve bottom-up; an SCC's constraints reference only itself and
   already-solved SCCs.
2. **Precise iteration to a threshold `k`.** Within an SCC, iterate `Φ` from `⊥ = 0`.
   Shallow structural recursion converges in 1–2 steps with an *exact* `β` — no
   widening, exact arena. This is the common case and it stays precise.
3. **Widening** (only if not converged by step `k`). Apply a widening operator
   `∇ : Bound × Bound → Bound` to force termination. Because `Bound` is `ℕ ∪ {ω}`, the
   canonical `∇` jumps a still-growing unknown to `ω`. Widening over-approximates
   *upward* → the **safe** direction for allocation (§2.3).
4. **Narrowing.** Re-descend from the widened post-fixpoint to recover precision
   widening discarded, tightening toward `lfp` without dropping below it.
5. **`ω` ⇒ stackful.** An unknown that settles at `ω` marks its SCC `div`: the backend
   emits the **growable-stack / stackful** lowering for that SCC specifically.

> **Quantitative-Atli contains qualitative-Atli as its `⊤` case.** Where step 2/4 yield
> a finite `β`, you get an exact arena. Where widening gives up (`ω`), you fall back to
> exactly the growable-stack path a purely-qualitative design would have used
> everywhere. One mechanism: exact where achievable, graceful where not.

### 7.3 Phase discipline (miscompilation guard)

Because pre-convergence iterates are *under-estimates* (§2.3), the compiler enforces:

- **Grades are write-only until their SCC is certified converged.** No pass may *read*
  a `β` for allocation before a convergence certificate exists for its SCC.
- **The backend consumes `β` strictly downstream of the per-SCC converged gate.**

This makes "no partial iterate reaches codegen" a *structural* property of phase
ordering, not a convention. It is the codegen-side twin of the checker-side discipline
"the reference interpreter is the oracle, not the checker's internal state."

---

## 8. Metatheory obligations

Stated as precise theorems. **[settled]** = follows standard technique once the rules
are fixed; **[novel]** = Atli-specific, the real work.

### 8.1 Progress (effectful) — **[settled]**
If `∅ ⊢ e : T ! ε` then exactly one of:

1. `e` is a value;
2. `e → e'` for some `e'`;
3. `e` is blocked on an unhandled operation predicted by its row: there exist
   `ℓ ∈ ε`, a value `v`, and an evaluation context `E` handler-free for `ℓ`, with
   `e = E[perform ℓ v]`.

**Corollary (effect-closed progress).** If `∅ ⊢ e : T ! ∅` then `e` is a value or
steps; the third disjunct is uninhabited at the empty row. Atli deliberately retains two
detectable stuck faces, each theorem-governed: resume-after-use is unreachable for
well-typed programs (§8.3), while unhandled-operation blocking is reachable only when
predicted by the effect row. This is the runtime face of `StuckUnhandledOperation` and
the theorem consumed by effect-closed `spawn` bodies.

### 8.2 Preservation — **[settled]**
If `∅ ⊢ e : T ! ε, β` and `e → e'` then `∅ ⊢ e' : T ! ε', β'` with `ε' ⊆ ε` and
`β' ⊑ β`. Effects only shrink or hold; `β` only holds or is over-approximated; region
narrows.

### 8.3 Affine continuations / no-duplication — **[settled given QTT]**
In a well-typed program no continuation `κ` is resumed more than once; equivalently, the
`resume`-after-use redex is unreachable. Follows from `[1]`-grading of `Cont` and the
substructural context discipline. *This is the lemma the reference interpreter tests
empirically at Layer 1 (§10).*

### 8.4 Boundedness soundness (the arena never overflows) — **[novel]**
> If `∅ ⊢ e : T ! ⟨ε; β; ρ⟩` with `β ∈ ℕ` (finite), then every continuation frame
> allocated during any reduction sequence of `e` fits within `β` bytes in region `ρ`.

The core safety theorem: the quantitative grade is a *true upper bound* on realized
frame size. Its proof rests on 8.3 (affine `k` ⇒ additive frame accounting) and on the
`Handle`/`Fix` rules' `β` bookkeeping.

### 8.5 Widening soundness (the inverted criterion) — **[novel]**
> For every unknown `βₓ`, the widened solution `β̃ₓ` satisfies `β̃ₓ ⊒ lfp(Φ)ₓ`
> (**never under-approximates**), and — with §7.3's phase gate as hypothesis — no
> pre-convergence iterate is observable by codegen.

⚠️ **Do not port a widening-soundness proof from a safety analysis unchanged.** The goal
predicate is `≥ true size`, not `⊆ safe set`. The direction is the point.

### 8.6 Principality — **[novel, the technical crux]**
> Algorithmic inference computes, for every typeable `e`, a type that is principal with
> respect to the declarative subtyping of §4.9 — where the effect component is
> minimized (covariant) and the boundedness component sits in contravariant position
> under the arrow.

The difficulty is the **variance mismatch at the arrow**: `ε` is a graded monad
(covariant with the result) and `β` is a graded comonad (contravariant with the
argument's context demand), yet both are inferred by one fixpoint solver. "Most general"
is defined w.r.t. a **mixed order** — `⊑` on the effect component, dual-position on the
boundedness component — and principality is the proof that the solver is monotone and
converges to the least element under *that* mixed order. Get the mixed order right and
monotone and principality follows; get it wrong and the solver either rejects typeable
programs or infers non-principal types that break composition.

Proof techniques come from the qualified-types tradition (soundness + principality of
constraint-based inference) even though the *solver engine* is bespoke rather than
`HM(X)`/`OutsideIn`.

---

## 9. Codegen contract

Each grade is a license the backend cashes:

| Grade | License |
|-------|---------|
| `q = 1` at `inplace` | emit in-place destructive update; no RC traffic on the target |
| `q = 1` at `move` | emit zero-copy ownership transfer across regions; elide the atomic refcount bump |
| `β ∈ ℕ` (finite) | emit a stackless frontend-split computation in a preallocated arena of exactly `β` **frame slots** plus the tier overhead `C` (§9.1); no heap fallback |
| `β = ω` (`div`) | emit the growable/stackful lowering for this SCC, or reject on tier-1 backends (§9.1) |
| `ρ` | select the arena; frame dies when `ρ`'s node in the spawn tree is cancelled/completes |
| `ε \ L = ∅` after all handlers | computation is pure at this point; standard optimizations unlocked |


### 9.1 Frame model, tier 1

This tier pins the unit of `β` for executable backends: **`β` counts frame slots, not
bytes**. One frame slot is one uniform machine word; in tier 1 that word is represented
as an `i64`. A frame is the per-activation record of either a `fix` call or a captured
continuation context. Its slot count is what the §7 boundedness constraints count.

Slot-counting is deliberately representation-independent. The same certified `β` can
be compared to the reference interpreter's frame-count proxy and to any backend whose
activation records fit in the slot model. Byte accuracy is a refinement: a later backend
may attach a target-specific `slot_size` map to frame fields, but that refinement must
prove it implements this slot metric rather than silently replacing it.

**Arena contract.** A computation checked with finite `β` executes within a
preallocated arena of exactly `β` frame slots plus a documented constant overhead `C`.
For tier 1, `C = 0`: the bump pointer, high-water counter, and diagnostic bookkeeping
live outside the certified arena and are not counted as program frame slots. Overflow of
this arena in a certified computation is a certified-grade soundness violation in the
§2.3 miscompile direction, not a recoverable slow path. Tier-1 backends must trap with a
distinguishable error if the bump would exceed `β + C`; the trap exists to falsify the
thesis if the certified bound is wrong.

**`Div` contract.** A computation with `β = ω` requires a growable lowering. Sprint 08's
tier-2 smoke backend starts with a 64-slot growable segment and may run under a bounded
test harness (`ATLI_MAX_ITERS`) to observe divergent programs without claiming finite
boundedness. Finite-β frames never use the growable segment; the checker-certified grade
selects the exact arena path versus the `ω` growable path.

**L7 hook.** The mechanized boundedness-soundness statement (§8.4/L7) quantifies over
this slot metric: every realized frame-slot prefix of a reduction from a term typed with
finite `β` is at most `β`. A byte-level theorem is a future refinement over the same
slot model.

### 9.2 Tier-1 data region

Arrays, records, and variants allocate in a data region separate from the certified `β`
arena. The `β` grade remains purely a control-frame slot bound: an aggregate handle stored
in a frame consumes one frame slot like any other machine-word value, but the aggregate
payload does **not** consume certified frame slots and does not affect the solver.

Tier-1 aggregate payloads are bump-allocated in a program-lifetime data region and freed
wholesale at process exit. This is leak-free by program death; reference counting,
Perceus-style reuse analysis, and early reclamation are future data-region refinements,
not requirements for the `q = 1` soundness claim.

Native execution reports `ATLI_DATA_ALLOCS=n`, counting aggregate creations and functional
copies. `mkarray`, record construction, and variant construction increment the count;
functional array `set` and functional record update increment the count because they
allocate shallow copies. `inplace set` and `inplace ⟨r | ℓ = e⟩` emit no allocation at the
update site and therefore do not increment the count. Out-of-bounds compiled aggregate
access traps with exit 88 and message `ATLI BOUNDS`, matching the oracle's bounds-error
outcome.

### 9.3 Tasks and the region tree

`scope` creates a region node and a task group; `spawn` creates a child task node. The
task tree, region tree, and structured-join tree are the same tree. A spawned task gets
its own control arena sized from the callee's certified `β`; if the callee is `Div`, it
uses the growable segment. Thus the allocation thesis is per task: the type computes each
task's stack budget before the OS thread exists.

Task data allocations live in the child data region nested under the enclosing scope's
region. Move-in is zero-copy: arguments are evaluated in the parent and a unique handle may
be transferred into the child without copying because the parent scope outlives all of its
children. Heap results cross back at `await` by a boundary copy into the awaiting scope's
region, counted in `ATLI_DATA_ALLOCS`; primitive results return directly. Zero-copy result
promotion is a future region-optimization, not the tier-1 rule.

Tier-1 cancellation is honest and simple: traps remain process-fatal (86/87/88), so
failure cancellation degenerates to "everything dies." The normative shape is still the
scope/task/region tree; cooperative cancellation will refine the behavior without changing
the ownership and outlives rules. Native execution reports `ATLI_TASKS_SPAWNED=n`, and
high-water reporting is the maximum across finite task arenas (debug builds may also report
per-task highs).


### 9.4 Generic erasure

Tier-1 polymorphism is erased. Every runtime value is already one uniform `i64` slot: a
Nat immediate, task handle, function placeholder, or data-region handle. A generic
function therefore compiles once and operates on slots; the checker guarantees that every
call site uses the erased slot consistently. There is no boxing and no dictionary passing
in tier 1.

Certified `β` is per function, not per instantiation. This is sound for the current slot
frame metric because the counted captures and activations are structural and
type-independent. The trigger that ends free erasure is the standing byte-accurate frame
refinement: once frames count backend-specific byte layouts rather than uniform slots,
`β` may become type-dependent and monomorphization becomes the implementation path.
ROADMAP tracks this as a paired item: **byte-accurate frames ⇒ monomorphization**. Spawn
of a generic callee uses the same per-function `CertifiedTaskBudget` path as monomorphic
callees.

**No LLVM coroutines.** Atli owns the continuation split in its own mid-end (Zig's hard-
won lesson: LLVM couples frame alloc/dealloc to execution, forcing heap-allocated self-
destroying frames — fatal to arena placement, and its splitting pass is slow and buggy).
Atli emits *plain functions and structs*; MLIR/LLVM never see a coroutine.

**WASM.** Where the engine supports **stack-switching** (`suspend`/`resume`/`switch` on
tags — co-designed with effect handlers), lower `perform`/`Handle` directly to it. Where
it does not (still experimental across engines as of 2026), lower the *same*
frontend-split representation to a self-hosted trampoline. One split, two backends,
selected per target.

---

## 10. Minimal mechanization target (do this first)

Mechanize in Rocq (Iris for the substructural/linearity reasoning). Prove soundness on a
**radically shrunk core** containing exactly the novel interaction and nothing else:

- Types: `Unit`, `Nat`, one arrow, `Cont`; `Nat` has unary `zero`/`succ` and `case`.
- Effects: finitely many labels `ℓᵢ`; Sprint 04's one-label Rocq scaffold is the base
  case. The L5 clause lemma is label-count independent because it is stated per clause.
- **One** handler form (`Handle`), deep, affine/relevant per-clause `kᵢ`, with lazy
  continuation capture for dropped clauses (`H-op-drop`), one-shot materialized
  continuations for resuming clauses (`H-op-resume`), and the lemma that typed clauses
  satisfy `kᵢ ∈ FV(eᵢ) ⇔ eᵢ` directly resumes `kᵢ` exactly once.
- Boundedness: `Bound = ℕ ∪ {ω}`, `⊕`/`⊔`, `Fix`/`fix*` with recursive `β` constraints.
- Drop for now in Rocq: records/variants, aggregate heap semantics, regions beyond a single
  arena, arrays, `move`, `inplace`, and `freeze`.

Arrays, records, variants, data-affinity, tasks, and parametric polymorphism are now part of the executable compiler
but remain outside the Rocq scaffold. The proof ladder therefore adds L9 as
`Stated-Pending-Infrastructure`: **uniqueness soundness**, the observational
equivalence of `inplace set` / in-place record replacement and their functional-copy counterparts under §4's affine discipline. Stating
and proving L9 requires graded contexts and a heap in the step relation; it is not an
`Admitted` theorem in the current scaffold and does not change `proofs/ADMITTED_COUNT`.
Sprint 13 adds L10 as `Stated-Pending-Infrastructure`: **schedule independence**, the
claim that well-typed task programs have the same observables under every fair native
interleaving and under the deterministic sequential oracle. Stating and proving L10
requires a concurrent small-step relation over task pools plus the region tree; it is not
an `Admitted` theorem and does not change `proofs/ADMITTED_COUNT`. Sprint 14 widens the
coverage boundary again: generics and `^u` require polymorphic typing plus graded type
variables before Rocq can state their preservation theorem; this is tracked as
mechanized-core coverage, not as an admitted proof.

Prove, in order of pain:
1. **8.6 principality** for this core (the mixed order; the crux).
2. **8.4 boundedness soundness** (arena never overflows) — depends on **8.3** (affine
   `k`), which Iris makes clean.
3. **8.5 widening soundness** — with the `≥ true size` goal and the §7.3 phase gate as
   hypothesis.
4. **8.1 / 8.2** progress & preservation — standard once the above hold. The latent row on
   arrows from §3.1/§4.2/§4.3 is load-bearing and is retained in the mechanized reduced
   core; finding nineteen showed that erasing it launders latent effects and `β` through
   higher-order calls.

In parallel, Layer‑1: build a **well-typed-term generator** from the rules above (writing
the generator *is* the first executable spec — it forces the rules to be precise enough
to sample) and property-test the checker for substitution, principality, confluence, and
preservation-as-a-step against the §5 reference interpreter.

---

## 11. Open questions (tracked, not blocking)

- **Mixed-order formalization (8.6).** Exact statement of the effect/coeffect variance
  order for arrows; whether a single lattice or a fibration is the cleanest carrier.
- **Widening operator choice.** Threshold `k`; whether narrowing is worth its own
  soundness proof or whether a bounded precise-iteration budget suffices in practice.
- **`⊕` for frames: `+` vs. context-sensitive `max`.** `+` is the sound
  over-approximation adopted here; a liveness-aware analysis could sometimes use `max`
  (frames that provably don't coexist) for tighter arenas — a precision optimization,
  not a soundness change.
- **`move` across regions in the presence of `div`.** Transferring a continuation whose
  own `β = ω` — semantics and cost.
- **Region grade metatheory.** Kept light in the core; the full spawn=arena=cancellation
  region system needs its own (standard) region-soundness pass when reintroduced.

---

## References (read `[Gab16]` before writing any code that touches §6)

- **[Gab16]** Gaboardi, Katsumata, Orchard, Breuvart, Uustalu. *Combining Effects and
  Coeffects via Grading.* ICFP 2016. — the combining operator §6 specializes.
- Orchard, Liepelt, Eades. *Quantitative Program Reasoning with Graded Modal Types*
  (Granule). ICFP 2019. — nearest existing type system; no systems backend.
- Petricek, Orchard, Mycroft. *Coeffects: A Calculus of Context-Dependent Computation.*
  ICFP 2014. — the comonadic/coeffect framing of `β`.
- Atkey. *Syntax and Semantics of Quantitative Type Theory.* LICS 2018. — the `Q`
  substructural grading and graded contexts.
- Cousot & Cousot. *Abstract Interpretation.* POPL 1977. — fixpoint/widening/narrowing
  (with the §2.3 caveat on inverted soundness).
- Reynolds/Tofte–Talpin region tradition; Verona regions — the `ρ` grade.
- Leijen. *Koka: effect types and handlers*; Xie & Leijen, *Perceus reference counting*
  — effect rows and RC-via-acyclicity precedent.
- WebAssembly stack-switching proposal (effect-handler-shaped `suspend`/`resume`/
  `switch`) — the WASM lowering target.
- Zig async / coroutine history (frontend splitting; the LLVM-coroutine frame-allocation
  problem) — engineering precedent for §9's "no LLVM coroutines."
