# Atli

**Atli** is a functional systems language with *one* syntax for systems code, network
services, and the browser — so you never switch mental models moving between them. It is
immutable by default, has no garbage collector, and makes manual memory safe through a
graded type system in which the types **compute your stack-frame allocation sizes**. It
compiles through MLIR to native and WebAssembly.

Roughly: Zig and Elixir had a baby, and it went to grad school for type theory.

> ⚠️ **Status: early design + spike.** Nothing runs yet. There is a formal core calculus
> ([`docs/calculus.md`](docs/calculus.md)) and a settled design; the compiler is being
> built spike-first. Syntax below is draft‑0 and provisional. See
> [Status & roadmap](#status--roadmap).

---

## Why

If you write Zig for the hot path, Elixir for the services, and TypeScript for the
frontend, the friction was never three syntaxes — it was three *memory-and-concurrency
models* that refuse to reconcile: manual/no‑GC, per‑process‑GC/immutable, and
either/whatever. Every context boundary is a mental‑model reload.

Atli's bet is that one language can span all three **if** it picks a single spine and
makes the whole thing legible: immutable functional core, effects for everything impure
(including concurrency), no tracing GC, and a type system where every property the
machine relies on is written in the source and checked at compile time. You get the
systems performance where you need it and the isolation/concurrency story where you need
that — without ever changing languages, or changing how you think about memory.

The through‑line, in one sentence: **the behavior of the machine is legible in the
source, and the type system turns that legibility into faster generated code.**

---

## A taste

A pure, total function has *zero* ceremony. The effect row and the boundedness grade are
there — they're just all-defaults, so nothing shows:

```atli
pub fn fib(n: Nat) -> Nat = case n {
  0 -> 0
  1 -> 1
  m -> fib(m - 1) + fib(m - 2)
}
```

Do something impure and the row surfaces — in the *signature*, not at the call site. The
contract carries the property; the body stays clean:

```atli
effect File {
  read(path: String) -> Bytes
  write(path: String, data: Bytes) -> Unit
}

pub fn load_config(path: String) -> Config ! {File} =
  File.read(path) |> parse
```

Effects are handled with algebraic handlers, and the continuation is a **one-shot linear
value** you can see being spent. Resume by calling `k` (at most once — twice is a type
error); drop `k` with `_` and you've written an exception / early return:

```atli
pub fn with_memory_fs[A](files: Map[String, Bytes], body: () -> A ! {File}) -> A =
  handle body() {
    return(x)              -> x
    File.read(path), k     -> k(Map.get(files, path))   // resume once
    File.write(path, _), k -> k(())
    // (a non-resuming clause would bind `_` and just not call it)
  }
```

And the piece that shows what the type system buys you. This reads like ordinary
immutable pipe‑chaining; it *compiles* to a mutable buffer being scribbled on in place —
zero copies, zero refcount traffic — because `buf` is unique (`^Image`) and each
`inplace` step is *licensed* by that uniqueness:

```atli
pub fn render(size: Nat) -> Image = {
  buf = Image.blank(size)          // buf : ^Image  — unique, arena-allocated
  buf
  |> inplace set(10, 10, Red)      // ^Image -> ^Image, mutates in place
  |> inplace set(20, 20, Blue)
  |> inplace fill_rect(0, 0, 5, 5, Green)
  |> freeze                        // ^Image -> Image  — forget uniqueness, return immutable
}
```

Functional on top, in‑place underneath, and the `^` in the type is the only tell.

---

## What makes it different

### Types are codegen licenses

Every grade Atli tracks is a *proof obligation the checker discharges so the backend can
emit code that would be unsafe without the proof.* This is the core idea the whole
language is organized around — grades aren't documentation, they pay rent in generated
code:

| The type proves… | …so the compiler may |
|------------------|----------------------|
| this reference is **unique** (`^`) | mutate in place (`inplace`); elide refcounts; move without copying |
| this computation's **frame is bounded** (a finite size) | allocate a **stackless frame of exactly that size in an arena** — no overflow guard, no growth check |
| the effect set is **empty** here | unlock the pure-code optimizations |
| this data structure is **acyclic** (it always is — immutability forbids cycles) | reference-count it with no tracing GC and no cycle collector |

The headline case: **boundedness is quantitative, and the number *is* the arena size.**
The type doesn't just prove "this terminates" — it computes how many bytes the
continuation frame needs, and that's what gets allocated. Where the compiler can't
compute a finite size, the function is `div` and gets a growable stack instead. Exact
where achievable, graceful where not.

### The capability row

Instead of scattering effects here, ownership there, and allocation implicitly, a single
**capability row** travels with every computation and records four things at once — what
it *does* (effects), what it *consumes* (uniqueness), what it *demands* (a frame size),
and *where* it lives (region/arena). One legible ledger of everything a function does to
the world. Under the hood it's a graded type system combining an effect monad and a
boundedness *coeffect*; the formal treatment is in [`docs/calculus.md`](docs/calculus.md).

Each of the three user-facing grades is the same three-rung ladder — **default (free) →
annotate (strengthen) → mark (escape)** — so you learn the shape once and apply it to
memory (`hope` / `inplace` / `uniq`), uniqueness (bare / `^` / `^u`), and termination
(structural / `measure` / `div`). You pay syntax only when you leave a default.

### One-shot continuations, arenas, no GC

Continuations are affine — resumed at most once. That single restriction is the keystone
holding up four subsystems simultaneously: memory safety (no aliasing a resumed frame),
simple frame representation (frames are consumed-once), sound termination checking under
effects, and a decidable type solver. Memory is reclaimed by reference counting made
*complete* by immutability (acyclic data can't leak through cycles) and *fast* by reuse
analysis (functional updates on uniquely-owned data become in-place mutation). Concurrent
tasks get per-task arenas, and **spawn = arena = cancellation** is one tree: cancel a
subtree and its arenas free as a single operation.

---

## How it lowers

Atli owns its continuation transform in its own mid‑end and emits **plain functions and
structs** — MLIR and LLVM never see a coroutine. (This is deliberate: LLVM coroutines
couple frame allocation to execution, forcing heap‑allocated self‑destroying frames,
which is fatal to arena placement. Zig learned this the hard way and moved the split into
its frontend; Atli starts there.)

From the shared mid‑end, the boundedness grade drives the choice: **bounded** frames
lower to stackless, arena-placed frames sized exactly by the grade; **`div`** frames
lower to a growable stack. On the backend:

- **Native** — MLIR → LLVM, arenas and a work‑stealing scheduler for the concurrency
  runtime.
- **WebAssembly** — where the engine supports the **stack‑switching** proposal
  (`suspend`/`resume`/`switch`, co‑designed with effect handlers), handlers lower almost
  1:1 onto it; where it doesn't yet, the *same* split representation lowers to a
  self‑hosted trampoline. One split, two backends, chosen per target.

---

## Status & roadmap

This repository is a design and a plan, not yet a working compiler. The design is
settled; the build is spike‑first, with verification treated as a first-class harness
rather than an afterthought.

**Done**
- Core language design (settled across every load-bearing fork).
- Formal core calculus `λ_Atli` — grade algebra, typing rules, the novel handler rule,
  boundedness fixpoint, and stated metatheory obligations:
  [`docs/calculus.md`](docs/calculus.md).
- Draft‑0 surface syntax (this README's snippets).

**Next (the spike, roughly in order)**
1. **Reference interpreter** for the core calculus — the operational oracle everything
   else is checked against.
2. **Well‑typed‑term generator** from the typing rules — the test engine, and the thing
   that forces the rules to be precise enough to sample from.
3. **Bespoke type checker** (kinded, bidirectional capability‑row solver with a
   quantitative‑boundedness fixpoint), property‑tested against 1 & 2.
4. **Mechanized soundness of the handler rule** in Rocq/Iris, on a radically shrunk core
   (one effect, one handler, affine continuation) — the one genuinely novel obligation.
5. **MLIR lowering** — native first, then WASM (stack‑switching + trampoline fallback).

**Not yet designed** (tracked, not blocking): the module system, the effect‑operation
signature namespace (open vs. closed rows), and the full region grade beyond a single
arena.

---

## Design docs

- [`docs/calculus.md`](docs/calculus.md) — the formal core: grade algebra, syntax,
  typing judgment, operational semantics, **the handler rule** (the novel contribution),
  the boundedness fixpoint + widening, metatheory obligations, and the minimal
  mechanization target. Start here if you want to understand or verify the type system.

---

## Prior art

Atli stands on a lot of existing work; its contribution is the *combination* and the
*systems backend*, not the individual pieces.

- **Granule** (Orchard et al.) — the nearest existing type system: graded modal types
  tracking effects *and* coeffects over a linear base. Atli's delta: quantitative
  boundedness where the grade is the arena size, a bespoke fixpoint solver (for compile
  speed and error quality), and an actual systems backend.
- **Combining Effects and Coeffects via Grading** (Gaboardi, Katsumata, Orchard,
  Breuvart, Uustalu — ICFP 2016) — the framework for composing a graded monad with a
  graded comonad. Atli's handler rule is this combining operator, specialized.
- **Koka / Perceus** (Leijen; Xie & Leijen) — effect handlers with row polymorphism, and
  reference counting with reuse analysis and no tracing GC.
- **Quantitative Type Theory** (Atkey) — the substructural `{0,1,ω}` grading and graded
  contexts.
- **Coeffects** (Petricek, Orchard, Mycroft) — the comonadic framing of context demand.
- **Abstract interpretation** (Cousot & Cousot) — the fixpoint/widening machinery for
  the boundedness solver (with a crucial inversion: here the analysis *sizes an
  allocation*, so the soundness direction flips).
- **Zig** — the systems sensibility, and the hard‑won engineering lesson that
  continuation splitting belongs in the frontend, not in LLVM coroutines.
- **MLIR / WebAssembly stack‑switching** — the lowering substrate and the effect‑shaped
  WASM control‑flow target.

---

## The name

**Atli** is the Norse name for Attila — short, sharp, and sitting comfortably next to
Odin in the tradition of naming systems languages after Norse figures. It also happens to
be the author's son's name.

The etymology turned out to fit the compiler: in the saga, Atli is the one who knows
exactly how large a hall he needs before the guests arrive. So does this one — it
computes the size of the frame before anything runs, and never allocates a byte it can't
account for.
