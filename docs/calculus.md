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

Join-semilattice. Sequential composition = `∪`. **Covariant** subsumption in the
grade: `T ! ε` coerces to `T ! ε'` when `ε ⊑ ε'` (a less-effectful computation is
usable as a more-effectful one). For principality, *minimize* `ε`.

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
value type      τ ::= Unit | Bool | Nat
                    | (T →[σ] T)               function; latent row σ fires on apply
                    | ⟨ ℓ:T, … ⟩               record
                    | [ ℓ:T | … ]              variant
                    | Cont[σ] T T              one-shot continuation (resume-type, answer-type)
                    | μα. τ  |  α              (structurally-bounded) recursive type

graded type     T ::= τ @ q                    value type with uniqueness grade q ∈ Q

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
    | λ x:T. e                        abstraction
    | e₁ e₂                           application
    | let x = e₁ in e₂                sequencing (monadic bind)
    | fix f:(T →[σ] T). λ x. e         recursion  (induces the β-constraint, §7)
    | ⟨ ℓ = e, … ⟩ | e.ℓ              record intro / proj
    | perform ℓ e                     invoke effect operation ℓ
    | handle e with H                 effect handler (deep)
    | resume k e                      invoke a captured continuation (consumes k)
    | move e                          transfer unique ownership (consumes e)
    | inplace e                       destructive update (requires q=1)

H ::= { return x → e_ret ; (ℓ p k → e_ℓ)* }
```

Handler `H` has one return clause and zero-or-more operation clauses. In clause
`ℓ p k → e_ℓ`, `p` binds the operation argument and `k : Cont[…] A R @ 1` names the
**one-shot** delimited continuation up to the enclosing `handle`. The continuation is
materialized lazily: a clause that does not use `k` does not allocate or carry the
delimited frame.

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
```

Both *require* `q = 1` in the premise. `move` re-issues a unique reference to a fresh
region (enabling zero-copy cross-task transfer, checked against `ρ`); `inplace`
licenses destructive mutation in the backend (§9). Neither is well-typed on a `ω`
(shared) value — that is a compile error naming the alias that forced sharing.

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
`β ⊒ Fix_β(f, e)`, whose least solution over `Bound` is computed in §7. For the
structural/free rung, the concrete strict-descent condition is: a recursive call may use
only a variable bound by a `succ x` pattern whose scrutinee is the current recursive
parameter. That variable is a strict subterm of the scrutinee because the `case` rule has
peeled one `succ`. If the resulting lfp is finite, the frame is statically sized
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
```

Handler reductions (deep):

```
handle v with H                →   e_r[x := v]                           (H-return)

handle E[perform ℓ v] with H   →   e_ℓ[ p := v ]                         (H-op-drop)
     when  ℓ ∈ H, E is handler-free for ℓ, and k ∉ FV(e_ℓ).
     No continuation is materialized; the captured frame is not allocated.

handle E[perform ℓ v] with H   →   e_ℓ[ p := v ,
                                        k := κ ]                         (H-op-resume)
     when  ℓ ∈ H, E is handler-free for ℓ, and k ∈ FV(e_ℓ), where
     κ  =  λ y. handle E[y] with H          -- deep: H reinstalled
     and κ is marked ONE-SHOT.

resume κ v                      →   κ v            if κ not yet used      (resume)
resume κ v                      →   ⊥ (stuck)      if κ already used      (one-shot violation)
```

The one-shot marking on materialized `κ` is the operational witness of the `[1]` grade in
`Handle`; dropped clauses have no `κ` to mark because lazy capture avoids allocation.
Preservation (§8.2) guarantees the stuck case is unreachable in well-typed programs;
it is retained so the reference interpreter can *detect* a violation during testing
(Layer‑1 property: "no well-typed program reaches `resume`-after-use").

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
substitution at recursive occurrences. For structural recursion over `Nat`, a recursive
occurrence is accepted at the free rung only when its argument is the predecessor variable
introduced by a surrounding `succ x` branch for the current recursive parameter. The
intended solution is the **least fixpoint** `lfp Φ` (tightest sound frame sizes).

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

### 8.1 Progress — **[settled]**
If `∅ ⊢ e : T ! σ` then `e` is a value or `e → e'`. (Note the `resume`-after-use stuck
state is excluded by 8.3.)

### 8.2 Preservation — **[settled]**
If `Γ ⊢ e : T ! σ` and `e → e'` then `Γ ⊢ e' : T ! σ'` with `σ' ⊑⁺ σ`. (Effects only
shrink or hold; `β` only holds or is over-approximated; region narrows.)

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
| `β ∈ ℕ` (finite) | emit a **stackless frontend-split frame of exactly `β` bytes, allocated in `ρ`'s arena**; no stack-overflow guard, no growth check, no heap fallback |
| `β = ω` (`div`) | emit the growable/stackful lowering for this SCC |
| `ρ` | select the arena; frame dies when `ρ`'s node in the spawn tree is cancelled/completes |
| `ε \ L = ∅` after all handlers | computation is pure at this point; standard optimizations unlocked |

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
- Effects: **one** operation `ℓ`.
- **One** handler form (`Handle`), deep, affine/relevant `k`, with lazy continuation
  capture for dropped clauses (`H-op-drop`), one-shot materialized continuations for
  resuming clauses (`H-op-resume`), and the lemma that typed clauses satisfy
  `k ∈ FV(e_ℓ) ⇔ e_ℓ` directly resumes `k` exactly once.
- Boundedness: `Bound = ℕ ∪ {ω}`, `⊕`/`⊔`, `Fix` with the recursive `β`-constraint.
- Drop for now: records/variants, regions beyond a single arena, `move`/`inplace`
  (add back as *known-sound extensions* once the core holds).

Prove, in order of pain:
1. **8.6 principality** for this core (the mixed order; the crux).
2. **8.4 boundedness soundness** (arena never overflows) — depends on **8.3** (affine
   `k`), which Iris makes clean.
3. **8.5 widening soundness** — with the `≥ true size` goal and the §7.3 phase gate as
   hypothesis.
4. **8.1 / 8.2** progress & preservation — standard once the above hold.

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
