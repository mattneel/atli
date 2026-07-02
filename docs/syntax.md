# Atli Syntax

> **Status: implemented subset + open list (v0.5.3).** This document began as draft-0.
> The v0.5.3 compiler implements the reduced surface listed below and keeps the rest in
> the Open list. Normative elaboration details live in [`docs/elaboration.md`](elaboration.md);
> the core semantics live in [`docs/calculus.md`](calculus.md).

## Implemented in v0.5.3

- `fn` / `pub fn` declarations, expression or block bodied, including rank-1 type parameters (`fn f[A](...)`).
- Types: `Unit`, `Nat`, `Array[A]` (bare `Array` aliases `Array[Nat]`), `Task[T]`, declared generic record/variant types, unique marker `^T`, uniqueness-preservation marker `^u T`, arrows, and concrete effect rows `! {A, B}`.
- Expressions: `()`, decimal naturals, variables, unary calls, curried multi-arg calls,
  blocks, `case n { 0 -> e0; p -> e1 }`, pipes, `+ - *` over `Nat` (`-` is monus),
  array builtins `mkarray/get/set/len`, records, variants, field projection/update, constructor and record patterns, and prefix `move`/`inplace`/`freeze`.
- Recursion: structural by default, `measure e` trusted by the reduced core, and `div`.
  Real Fibonacci uses `measure`; arithmetic calls like `m - 1` are not the peeled
  predecessor required by strict structural recursion.
- Effects: multiple `effect L { op(x: Nat) -> Nat }` declarations, `L.op(e)`, and
  multi-label handlers with `k` or `_` continuation clauses.
- Mutual top-level recursion: declaration SCCs elaborate to core `fix*` groups.
- Aggregate declarations: nominal generic records and variants, exhaustive constructor cases, record destructuring, functional update, and in-place record replacement.
- Structured concurrency: `scope { ... }`, `spawn f(args)` for top-level functions, opaque
  affine task handles, and `await h`.
- Example-test directives in leading comments: `expect`, `expect-oracle`,
  `expect-compiled`, `expect-check-error`, and `env`.

## Still open

Full numeric tower, strings/chars/floats as runtime values, modules/`use`, byte-accurate
frame layout, monomorphization, bounded polymorphism/traits, effect-row variables/open
rows, real measure verification, and the full region grade remain future work.
Unsupported v0.5.3 constructs diagnose as "not yet in the reduced surface".

---

## 1. Lexical structure

### Comments

```zig
// line comment
/// doc comment (attaches to the following declaration)
```

No block comments — nesting comments hide structure, and Atli's whole premise is that
structure is legible.

### Naming convention (load-bearing)

Casing is not cosmetic; it tells you what kind of thing a name is, and — crucially — how
variables in a signature are bound:

| Form | Kind | Binding |
|------|------|---------|
| `snake_case` | values, functions, fields, operations | ordinary |
| `PascalCase` | types, effects, variant constructors | ordinary |
| `PascalCase` short (`A`, `B`, `K`, `V`) | **type** variables | declared explicitly in `[...]` |
| `lowercase` (`e`, `u`, `r`) | **grade** variables (effect-row, uniqueness, region) | **implicitly bound** per signature |

So `map[A, B](xs: ^u List[A], f: A -> B ! e)` declares type variables `A, B` in the
brackets, and *uses* grade variables `u` (uniqueness) and `e` (effect row) that are bound
implicitly by appearing. The common case — no grade variables — needs no brackets and no
ceremony.

### Literals

```zig
42            // Nat / Int
1_000_000     // underscores allowed
0xFF  0o17  0b1010
3.14  1.0e10  // F64
true  false
"hello"       // String, with \n \t \" \\ escapes
'a'           // single character
()            // Unit
```

### Keywords

```
pub fn effect handle case if else
spawn scope await move inplace freeze
measure div return type use and or not
```

### Operators

```
+  -  *  /  %            arithmetic
== != <  <= >  >=        comparison
and or not               boolean (words — `!` is reserved for effect rows)
|>                       pipe
->                       function type, case arm
=                        binding
^                        unique (prefix)
!                        effect-row marker (in signatures)
```

---

## 2. Bindings and blocks

Bindings are immutable and use bare `=` (no `let`). A block `{ … }` is an expression; its
value is its final expression. Statements are newline-separated; no semicolons required.

```zig
fn area(w: Nat, h: Nat) -> Nat = w * h        // expression-bodied

fn describe(p: Point) -> String = {           // block-bodied
  a = area(p.w, p.h)                           // immutable binding
  label = if a > 100 { "big" } else { "small" }
  label                                        // block's value
}
```

There is no rebinding of a name in the same scope. Shadowing in a nested scope is allowed.

---

## 3. Types

### Primitives

```zig
Unit  Bool  Nat  Int
U8 U16 U32 U64  I8 I16 I32 I64  F32 F64
String  Char
```

### Functions and the capability row

The signature is where legibility lives. Full shape:

```
[pub] fn NAME [ '[' TYPE_PARAMS ']' ] '(' PARAMS ')' '->' RET
      [ '!' EFFECT_ROW ]           // effects   — absent ⇒ pure
      [ BOUNDEDNESS ]              // measure/div — absent ⇒ structural, inferred
      ( '=' EXPR | BLOCK )
```

The two optional slots are the non-default rungs of their ladders. Absent = the free
rung (pure, structurally-bounded). Present = you left a default and said why.

Function *types* (as values/params) drop the name:

```zig
A -> B                    // single arg
(A, B) -> C               // multiple
() -> C                   // thunk / zero-arg
A -> B ! {File}           // with a concrete effect row
A -> B ! e                // with an effect-row variable
```

### Effect rows

```zig
! {File}                  // concrete: performs File operations
! {File, Net}             // concrete set
! e                       // variable: "whatever the caller/argument performs"
! {File | e}              // open row: File, plus whatever e carries
```

### Records

```zig
type Point  = { x: Int, y: Int }
type Config = { host: String, port: Nat }
```

Literal (Zig-style `.{ … }`, which disambiguates from a block), field access with `.`,
field punning in patterns:

```zig
origin = .{ x = 0, y = 0 }
px     = origin.x
```

### Variants (sums)

```zig
type Color     = Red | Green | Blue
type Option[A] = None | Some(A)   // generic variants are implemented in v0.5.3
type Shape     = Circle(Nat) | Rect(Nat, Nat)
```

### Generics

Type application uses brackets, uniformly for declarations and uses:

```zig
List[A]   Map[K, V]   Option[A]
fn first[A](xs: List[A]) -> Option[A] = ...
```

### Uniqueness markers

`^T` is a **unique** reference to `T` (exactly one live reference). `^u T` carries a
uniqueness *variable* `u` so a function can thread uniqueness end-to-end (unique-in ⇒
unique-out, shared-in ⇒ shared-out) without being written twice:

```zig
^Image                    // a unique Image
^u List[A]                // uniqueness-polymorphic list
```

Forgetting uniqueness (`^T` → `T`) happens by subsumption and **consumes** the unique
binding in v0.5.3: after a shared use there is no remaining unique handle to mutate. Write
`freeze e` when that shared handoff is intentional.

### Recursive types

Self-referential `type` declarations. Structural recursion over them is exactly what the
boundedness checker accepts for free:

```zig
type Tree[A] = Leaf | Node(Tree[A], A, Tree[A])
```

---

## 4. Functions

```zig
pub fn fib(n: Nat) -> Nat = case n {          // pure, total, zero ceremony
  0 -> 0
  1 -> 1
  m -> fib(m - 1) + fib(m - 2)
}

pub fn map[A, B](xs: List[A], f: A -> B ! e) -> List[B] ! e = case xs {
  []       -> []
  [x | rest] -> [f(x) | map(rest, f)]         // ! e threads the argument's effects
}
```

`pub` exports; its absence keeps the function module-private.

---

## 5. Expressions

### Application and pipes

```zig
parse(File.read(path))
File.read(path) |> parse |> validate         // left-to-right; x |> f(a) == f(x, a)
```

`x |> f(a, b)` threads `x` as the *first* argument: `f(x, a, b)`. Prefix forms thread
into the prefixed expression: `x |> inplace set(i, v)` is `inplace set(x, i, v)`, and
`x |> freeze` / `x |> move` are `freeze x` / `move x`.

### `if`

An expression; both branches must produce the same type (unless it's `Unit`):

```zig
label = if n > 100 { "big" } else if n > 10 { "medium" } else { "small" }
```

### `case` and pattern matching

```zig
case value {
  0            -> "zero"
  n if n < 0   -> "negative"                  // guard with `if`
  _            -> "positive"
}

case shape {
  Circle(r)    -> 3 * r * r
  Rect(w, h)   -> w * h
}

case xs {
  []              -> "empty"
  [x]             -> "one"
  [a, b | rest]   -> "many"                   // list cons patterns
}

case point {
  .{ x = 0, y = 0 } -> "origin"
  .{ x, y }         -> render(x, y)           // field punning binds x, y
}
```

Patterns: literals, `_` wildcard, variable binding, constructors (`Some(x)`), lists
(`[]`, `[h | t]`, `[a, b | rest]`), tuples (`(a, b)`),
and `pattern if guard`.

### Lists and tuples

```zig
xs    = [1, 2, 3]
pair  = (1, "two")                            // tuple; type (Nat, String)
```

---

## 6. Effects and handlers

### Declaring an effect

An effect is a named set of operations; each operation's declared return type is the
value a handler feeds back when it resumes:

```zig
effect File {
  read(path: String) -> Bytes
  write(path: String, data: Bytes) -> Unit
}

effect State[S] {
  get() -> S
  put(s: S) -> Unit
}
```

### Performing

Performing an operation is just a qualified call — the effect is tracked by the type, not
by a keyword at the site:

```zig
pub fn load_config(path: String) -> Config ! {File} =
  File.read(path) |> parse
```

### Handling

`handle EXPR { … }`. The `return` clause maps the final value (optional; defaults to
identity). Each operation clause binds the operation's arguments **and** the continuation
`k` after a comma. `k` is a **one-shot linear value**: call `k(v)` to resume (at most
once — twice is a type error); bind `_` and don't call it to write an exception / early
return.

```zig
pub fn with_memory_fs[A](files: Map[String, Bytes], body: () -> A ! {File}) -> A =
  handle body() {
    return(x)              -> x
    File.read(path), k     -> k(Map.get(files, path))   // resume once
    File.write(path, _), k -> k(())
  }

pub fn or_default[A](default: A, body: () -> A ! {Fail}) -> A =
  handle body() {
    return(x)      -> x
    Fail.fail(_), _ -> default                          // drop k ⇒ non-resumption
  }
```

Handlers are **deep**: the continuation `k` reinstalls the same handler, so effects
performed *after* a resume are handled too.

---

## 7. Memory and uniqueness

Immutable by default. Mutation and ownership transfer are explicit, and each is
*licensed* by the type:

- `^T` — a unique reference (see §3).
- `inplace EXPR` — perform an update destructively in place. Requires the target be
  unique; the type system's uniqueness proof is what makes this sound.
- `move EXPR` — transfer unique ownership (e.g. handing a buffer to another task), zero
  copy, sender provably loses access.
- `freeze EXPR` — coerce `^T` to `T`, ending a mutation chain. Often optional (the
  coercion is automatic by subsumption); written for clarity.

```zig
pub fn render(size: Nat) -> Image = {
  buf = Image.blank(size)          // buf : ^Image  — unique, arena-allocated
  buf
  |> inplace set(10, 10, Red)      // ^Image -> ^Image, mutates in place, no copy
  |> inplace set(20, 20, Blue)
  |> inplace fill_rect(0, 0, 5, 5, Green)
  |> freeze                        // ^Image -> Image, hand back immutable
}
```

The uniqueness-polymorphic combinator, so `map` composes into a unique pipeline while
ordinary callers never see the `u`:

```zig
pub fn map[A, B](xs: ^u List[A], f: A -> B) -> ^u List[B] = ...
```

---

## 8. Recursion and boundedness

The boundedness ladder, surfaced only at the two non-default rungs:

**Structural (default, free).** Recursion on a strict sub-term of a parameter — the tail
of a list, a child of a tree, `n - 1` of a `Nat`. No annotation; the frame is inferred to
a finite size and lowers to a stackless, arena-placed frame.

```zig
pub fn sum(xs: List[Nat]) -> Nat = case xs {
  []       -> 0
  [x | rest] -> x + sum(rest)                 // structural: no annotation
}
```

**`measure E` (annotated).** When descent isn't structural, supply a measure that
strictly decreases:

```zig
pub fn log2(n: Nat) -> Nat measure n = case n {   // recurses on n / 2
  0 -> 0
  m -> 1 + log2(m / 2)
}
```

**`div` (marked escape).** Genuinely unbounded computations — event loops, servers,
REPLs — mark `div`. The frame size is `ω`; the backend emits a growable stack for this
function specifically.

```zig
pub fn serve(sock: Socket) -> Never ! {Net} div = scope {
  loop {
    conn = Net.accept(sock)
    spawn handle_conn(conn)
  }
}
```

Signature slot order, left to right: `-> RET ! EFFECTS BOUNDEDNESS =`.

---

## 9. Concurrency

Concurrency is surfaced through `scope`, `spawn`, and `await`. `scope { … }` bounds child
task lifetimes: when the scope exits, its children are joined and the scope's region frees
as one operation. `spawn f(args)` starts a task whose callee is a declared top-level `fn`;
closures are not spawnable in v0.5.3. `await h` consumes an opaque affine task handle and
returns the task result. This is the surface of **spawn = arena = cancellation**: the task
tree, the arena tree, and the cancellation tree are the same tree.

```zig
fn work(n: Nat) -> Nat = n + 1

fn main() -> Nat = scope {
  h = spawn work(4)
  await h
}
```

Cross-task hand-off of a large buffer without copying uses `move` (§7): the sending task
provably loses access, the receiver gains a unique reference, no copy, no shared refcount.

Task handles are local-only: they may not be stored in aggregates or arrays, returned, or
passed to `spawn`. Spawned functions must be effect-closed; each task handles its own
effects. A dropped handle is joined at scope exit and its result is discarded.

---

## 10. Modules

**Not yet designed.** Working assumption: one file is one module, `pub` controls exports,
and `use` imports — but the import grammar, visibility beyond `pub`, and how effects and
grade variables cross module boundaries are open. Placeholder only:

```zig
use std.io
use std.collections.{ Map, List }
```

---

## Appendix A: Grammar sketch

Indicative EBNF, not yet complete or conflict-checked.

```
program     ::= decl*
decl        ::= ['pub'] fn_decl | type_decl | effect_decl | use_decl

fn_decl     ::= ['pub'] 'fn' NAME type_params? '(' params? ')' '->' type
                effect_row? boundedness? ('=' expr | block)
type_params ::= '[' NAME (',' NAME)* ']'
params      ::= param (',' param)*
param       ::= NAME ':' type
effect_row  ::= '!' ('{' row_elems? '}' | GRADE_VAR)
row_elems   ::= EFFECT (',' EFFECT)* ('|' GRADE_VAR)?
boundedness ::= 'measure' expr | 'div'

type_decl   ::= 'type' NAME type_params? '=' type_rhs
type_rhs    ::= record_ty | variant_ty | type
record_ty   ::= '{' (NAME ':' type)* '}'
variant_ty  ::= ctor ('|' ctor)*
ctor        ::= NAME ('(' type (',' type)* ')')?

effect_decl ::= 'effect' NAME type_params? '{' op_sig* '}'
op_sig      ::= NAME '(' params? ')' '->' type

type        ::= '^' GRADE_VAR? type_atom
              | type_atom '->' type
              | '(' type (',' type)* ')' '->' type
type_atom   ::= PRIM | NAME type_args? | '(' type (',' type)* ')' | '(' ')'
type_args   ::= '[' type (',' type)* ']'

block       ::= '{' stmt* expr? '}'
stmt        ::= NAME '=' expr
expr        ::= literal | NAME | app | pipe | if_expr | case_expr
              | record_lit | list_lit | tuple_lit | handle_expr
              | 'move' expr | 'inplace' expr | 'freeze' expr | 'spawn' expr
              | 'await' expr | 'scope' block | block
app         ::= expr '(' args? ')'
pipe        ::= expr '|>' expr
if_expr     ::= 'if' expr block ('else' (if_expr | block))?
case_expr   ::= 'case' expr '{' case_arm+ '}'
case_arm    ::= pattern ('if' expr)? '->' expr
handle_expr ::= 'handle' expr '{' handle_clause+ '}'
handle_clause ::= 'return' '(' NAME ')' '->' expr
              | EFFECT '.' NAME '(' patterns? ')' ',' (NAME | '_') '->' expr
record_lit  ::= '.{' (NAME '=' expr)* '}'
```

---

## Appendix B: Settled vs open

**Settled**
- Explicit one-shot continuation in handlers (`, k`), resumed by `k(v)`, dropped with `_`.
- Braces for blocks; free-form (not layout-sensitive).
- Naming convention: PascalCase type variables declared in `[...]`; lowercase grade
  variables bound implicitly.
- `=` immutable bindings, no `let`; blocks are expressions.
- Effect rows `{…}` / variable / `{… | e}`; boundedness `measure`/`div`; slot order.
- `^` / `^u` for uniqueness; `inplace` / `move` / `freeze`.
- `.{ … }` record literals and `.{ r | field = e }` update forms (disambiguate from blocks).

**Open**
- **Effect-operation namespace: open vs closed rows.** Must every effect be declared with
  `effect`, or can rows be extended/ad-hoc? Syntax (`{File | e}`) supports extension; the
  semantics (and whether `perform` of an undeclared operation is allowed) is undecided.
- **Region (`ρ`) surface.** Fully inferred today; the rare cross-arena `move` may want an
  explicit region annotation (`in r`?). Unspecified.
- **Module system** in full (§10).
- **Surface `Int` semantics.** Sprint 06 gives `Nat` subtraction monus semantics; signed
  `Int` arithmetic remains future work.
- **Effect-row variables/open rows.** The blocked target is `map[A, B](xs: List[A], f: A -> B ! e) -> List[B] ! e`; v0.5.3 generic higher-order arguments are pure. Syntax `! e` / `! {L | e}` remains open until row unification lands.
