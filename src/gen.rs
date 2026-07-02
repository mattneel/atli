//! Type-directed compositional term generation for Sprint 02.
//!
//! Generation follows the reduced typing rules in `docs/calculus.md §4`: the builder is
//! given a target type, a typing environment, and a depth budget, then recursively chooses
//! introduction/elimination forms for that target. The invariant is that every generated
//! **safe** term is closed, well-typed at its target type, and uses each continuation
//! variable at most once. Explicitly tagged negatives cover unhandled operations and the
//! aggregate affinity mistakes from `docs/calculus.md §4.2`. Shrinking is by choice bytes:
//! a shrunk choice sequence regenerates the term and then re-runs `derive_witness`, so
//! witness metadata is never stale.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{
    ContinuationUseFacts, CoverageTag, Divergence, ExpectedOutcome, FixBinding, GeneratedTerm,
    GenerationFacts, Handler, OpClause, RecursionTag, Term, Type, Witness,
};
use crate::grade::{Bound, Eff, Label, Region};

pub const FIXED_SEED: u64 = 0xA711_0002;
pub const SAMPLE_SIZE: usize = 1024;
pub const STEP_BUDGET: usize = 96;
pub const MAX_DEPTH: usize = 5;
pub const MAX_CHOICES: usize = 80;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenInput {
    pub choices: Vec<u8>,
}

impl GenInput {
    #[must_use]
    pub fn new(choices: Vec<u8>) -> Self {
        let choices = if choices.is_empty() { vec![0] } else { choices };
        Self { choices }
    }
}

#[must_use]
pub fn generated_case(selector: u8) -> GeneratedTerm {
    generated_from_choices(vec![
        selector,
        selector.wrapping_mul(17),
        selector.wrapping_add(91),
    ])
}

#[must_use]
pub fn generated_from_input(input: GenInput) -> GeneratedTerm {
    generated_from_choices(input.choices)
}

#[must_use]
pub fn generated_from_choices(choices: Vec<u8>) -> GeneratedTerm {
    match choices.first().copied() {
        Some(246) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "scope_spawn_await",
                builder.gen_scope_spawn_await(),
                ExpectedOutcome::Safe,
            );
        }
        Some(247) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "scope_spawn_dropped_handle",
                builder.gen_scope_spawn_dropped_handle(),
                ExpectedOutcome::Safe,
            );
        }
        Some(250) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "record_construct_peek",
                builder.gen_record_construct_peek(),
                ExpectedOutcome::Safe,
            );
        }
        Some(251) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "record_functional_update",
                builder.gen_record_functional_update(),
                ExpectedOutcome::Safe,
            );
        }
        Some(252) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "record_inplace_update",
                builder.gen_record_inplace_update(),
                ExpectedOutcome::Safe,
            );
        }
        Some(253) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "destructure_consume_chain",
                builder.gen_destructure_consume_chain(),
                ExpectedOutcome::Safe,
            );
        }
        Some(254) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "array_inplace",
                builder.gen_array_inplace(),
                ExpectedOutcome::Safe,
            );
        }
        Some(255) => {
            let mut builder =
                Builder::new(ChoiceStream::new(choices.into_iter().skip(1).collect()));
            return build(
                "variant_structural_fold",
                builder.gen_variant_structural_fold(),
                ExpectedOutcome::Safe,
            );
        }
        _ => {}
    }
    let mut builder = Builder::new(ChoiceStream::new(choices));
    let top_choice = builder.choices.next_mod(17);
    let mut expected = ExpectedOutcome::Safe;
    let (name, term) = match top_choice {
        0 => (
            "unit",
            builder.gen_term(&Type::Unit, &Env::default(), MAX_DEPTH),
        ),
        1 => (
            "nat",
            builder.gen_term(&Type::Nat, &Env::default(), MAX_DEPTH),
        ),
        2 => (
            "lambda_app",
            builder.gen_lambda_app(&Env::default(), MAX_DEPTH),
        ),
        3 => ("let", builder.gen_let_nat(&Env::default(), MAX_DEPTH)),
        4 => ("case", builder.gen_case_nat(&Env::default(), MAX_DEPTH)),
        5 => (
            "structural_fix",
            builder.gen_fix_app(RecursionTag::Structural, MAX_DEPTH),
        ),
        6 => (
            "measure_fix",
            builder.gen_fix_app(RecursionTag::Measure, MAX_DEPTH),
        ),
        7 => ("div_fix", builder.gen_fix_app(RecursionTag::Div, MAX_DEPTH)),
        8 => (
            "handle_resuming",
            builder.gen_handle(MAX_DEPTH, true, false),
        ),
        9 => (
            "handle_dropped",
            builder.gen_handle(MAX_DEPTH, false, false),
        ),
        10 => ("nested_handle", builder.gen_handle(MAX_DEPTH, true, true)),
        11 => (
            "multi_label_transparent",
            builder.gen_multi_label_transparent(),
        ),
        12 => (
            "multi_label_clause_set",
            builder.gen_multi_label_clause_set(),
        ),
        13 => (
            "fix_group_measure",
            builder.gen_fix_group(RecursionTag::Measure),
        ),
        14 => ("scope_spawn_await", builder.gen_scope_spawn_await()),
        15 => (
            "scope_spawn_dropped_handle",
            builder.gen_scope_spawn_dropped_handle(),
        ),
        _ => {
            expected = ExpectedOutcome::UnhandledOperation;
            (
                "negative_unhandled_perform",
                Term::Perform(Label::L, Box::new(builder.gen_pure_nat(2))),
            )
        }
    };
    build(name, term, expected)
}

#[must_use]
pub fn fixed_seed_inputs() -> Vec<GenInput> {
    let mut state = FIXED_SEED;
    (0..SAMPLE_SIZE)
        .map(|case| {
            let mut choices = Vec::with_capacity(MAX_CHOICES);
            let forced = match case {
                0 => Some(250),
                1 => Some(251),
                2 => Some(252),
                3 => Some(253),
                4 => Some(254),
                5 => Some(255),
                6 => Some(246),
                7 => Some(247),
                _ => None,
            };
            choices.push(forced.unwrap_or((case % 17) as u8));
            for _ in 1..MAX_CHOICES {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                choices.push((state >> 32) as u8);
            }
            GenInput::new(choices)
        })
        .collect()
}

#[must_use]
pub fn fixed_seed_sample() -> Vec<GeneratedTerm> {
    fixed_seed_inputs()
        .into_iter()
        .map(generated_from_input)
        .collect()
}

#[must_use]
pub fn coverage_counts(sample: &[GeneratedTerm]) -> BTreeMapCounts {
    let mut counts = BTreeMapCounts::default();
    for generated in sample {
        for tag in &generated.witness.coverage {
            counts.increment(*tag);
        }
    }
    counts
}

#[must_use]
pub fn distribution(sample: &[GeneratedTerm]) -> Distribution {
    let mut distribution = Distribution::default();
    for generated in sample {
        *distribution
            .depth_histogram
            .entry(generated.facts.depth)
            .or_default() += 1;
        distribution.nested_handlers += usize::from(generated.facts.nested_handlers);
        distribution.strict_rec_calls += generated.facts.strict_rec_calls;
        distribution.non_strict_rec_calls += generated.facts.non_strict_rec_calls;
        if generated.expected == ExpectedOutcome::UnhandledOperation {
            distribution.negative_unhandled += 1;
        }
    }
    distribution
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Distribution {
    pub depth_histogram: BTreeMap<usize, usize>,
    pub nested_handlers: usize,
    pub strict_rec_calls: usize,
    pub non_strict_rec_calls: usize,
    pub negative_unhandled: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggregateNegativeFixture {
    pub name: &'static str,
    pub source: &'static str,
    pub expected_error: &'static str,
}

#[must_use]
pub fn aggregate_negative_fixtures() -> Vec<AggregateNegativeFixture> {
    vec![
        AggregateNegativeFixture {
            name: "heap_field_projection_from_unique",
            source: "type Mailbox = { buf: Array, len: Nat }\nfn main() -> Nat = { m = .{ buf = mkarray(1, 0), len = 1 }\nget(m.buf, 0) }\n",
            expected_error: "heap-typed",
        },
        AggregateNegativeFixture {
            name: "use_after_destructure",
            source: "type Mailbox = { buf: Array, len: Nat }\nfn main() -> Nat = { m = .{ buf = mkarray(1, 0), len = 1 }\nx = case m { .{ buf, len } -> len }\nx + m.len }\n",
            expected_error: "consumed here",
        },
        AggregateNegativeFixture {
            name: "nonexhaustive_variant_case",
            source: "type Shape = Circle(Nat) | Rect(Nat, Nat)\nfn area(s: Shape) -> Nat = case s { Circle(r) -> r }\nfn main() -> Nat = area(Rect(3, 4))\n",
            expected_error: "missing constructors",
        },
        AggregateNegativeFixture {
            name: "inplace_update_on_shared_record",
            source: "type Box = { x: Nat, y: Nat }\nfn main() -> Nat = { b = freeze .{ x = 1, y = 2 }\nc = inplace .{ b | x = 7 }\nc.x }\n",
            expected_error: "requires unique",
        },
        AggregateNegativeFixture {
            name: "structural_fold_non_payload_argument",
            source: "type NatList = Nil | Cons(Nat, NatList)\nfn bad(xs: NatList) -> Nat = case xs { Nil -> 0; Cons(x, rest) -> bad(xs) }\nfn main() -> Nat = bad(Nil)\n",
            expected_error: "peeled predecessor",
        },
    ]
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BTreeMapCounts(BTreeMap<CoverageTag, usize>);

impl BTreeMapCounts {
    pub fn increment(&mut self, tag: CoverageTag) {
        *self.0.entry(tag).or_default() += 1;
    }

    #[must_use]
    pub fn get(&self, tag: CoverageTag) -> usize {
        self.0.get(&tag).copied().unwrap_or(0)
    }

    #[must_use]
    pub fn all_required_present(&self) -> bool {
        REQUIRED_COVERAGE.iter().all(|tag| self.get(*tag) > 0)
    }
}

pub const REQUIRED_COVERAGE: [CoverageTag; 7] = [
    CoverageTag::LambdaApp,
    CoverageTag::Let,
    CoverageTag::FixStructural,
    CoverageTag::FixMeasure,
    CoverageTag::Perform,
    CoverageTag::HandleResuming,
    CoverageTag::HandleDropped,
];

#[must_use]
pub fn derive_witness(term: &Term) -> Witness {
    derive(term, &Env::default()).into_witness()
}

fn build(name: &'static str, term: Term, expected: ExpectedOutcome) -> GeneratedTerm {
    let witness = derive_witness(&term);
    let facts = analyze_facts(&term);
    debug_assert_eq!(witness.coverage, derive_witness(&term).coverage);
    debug_assert!(witness.continuation_uses.resumed <= witness.continuation_uses.introduced);
    debug_assert!(is_closed(&term), "generated term must be closed: {term}");
    debug_assert!(
        term_obeys_continuation_usage(&term),
        "generated term violates handler k usage discipline: {term}"
    );
    GeneratedTerm {
        term,
        witness,
        name,
        expected,
        facts,
    }
}

/// Checks the reduced-core handler side condition from `docs/calculus.md §4.7`.
///
/// A handler clause may drop `k` by not mentioning it. If `k` appears free in the clause,
/// the only legal mention is exactly one direct `resume k v`. This makes the interpreter's
/// lazy `H-op-drop` / `H-op-resume` FV dispatch (`§5`) agree with derived β accounting on
/// generated well-typed terms.
#[must_use]
pub fn term_obeys_continuation_usage(term: &Term) -> bool {
    term_obeys_continuation_usage_under(term)
}

#[derive(Debug, Clone)]
struct ChoiceStream {
    choices: Vec<u8>,
    index: usize,
}

impl ChoiceStream {
    fn new(choices: Vec<u8>) -> Self {
        Self {
            choices: if choices.is_empty() { vec![0] } else { choices },
            index: 0,
        }
    }

    fn next(&mut self) -> u8 {
        let byte = self.choices[self.index % self.choices.len()];
        self.index += 1;
        byte
    }

    fn next_mod(&mut self, modulo: u8) -> u8 {
        debug_assert!(modulo > 0);
        self.next() % modulo
    }
}

#[derive(Debug, Clone)]
struct Builder {
    choices: ChoiceStream,
    fresh: usize,
}

impl Builder {
    fn new(choices: ChoiceStream) -> Self {
        Self { choices, fresh: 0 }
    }

    fn fresh_name(&mut self, prefix: &str) -> String {
        let name = format!("{prefix}{}", self.fresh);
        self.fresh += 1;
        name
    }

    fn gen_term(&mut self, target: &Type, env: &Env, depth: usize) -> Term {
        match target {
            Type::Unit => self.gen_unit(env, depth),
            Type::Nat => self.gen_nat(env, depth),
            Type::Array => Term::MkArray(Box::new(Term::nat(0)), Box::new(Term::nat(0))),
            Type::Task(result) => Term::TaskValue(Box::new(self.gen_term(
                result,
                env,
                depth.saturating_sub(1),
            ))),
            Type::Arrow(arg, ret) => {
                let param = self.fresh_name("x");
                Term::Lam {
                    param: param.clone(),
                    param_ty: (**arg).clone(),
                    body: Box::new(self.gen_term(
                        ret,
                        &env.with_var(param, (**arg).clone()),
                        depth.saturating_sub(1),
                    )),
                }
            }
            Type::Cont(_, _) => env
                .vars_of_type(target)
                .first()
                .map_or(Term::Cont(crate::core::ContId(0)), Term::var),
        }
    }

    fn gen_unit(&mut self, env: &Env, depth: usize) -> Term {
        if depth == 0 || self.choices.next_mod(3) == 0 {
            return env
                .vars_of_type(&Type::Unit)
                .first()
                .map_or(Term::unit(), Term::var);
        }
        let var = self.fresh_name("u");
        Term::Let {
            var: var.clone(),
            expr: Box::new(self.gen_nat(env, depth - 1)),
            body: Box::new(self.gen_unit(&env.with_var(var, Type::Nat), depth - 1)),
        }
    }

    fn gen_nat(&mut self, env: &Env, depth: usize) -> Term {
        if depth == 0 {
            return self.gen_nat_base(env);
        }
        match self.choices.next_mod(10) {
            0 => self.gen_nat_base(env),
            1 => Term::succ(self.gen_nat(env, depth - 1)),
            2 => self.gen_let_nat(env, depth),
            3 => self.gen_case_nat(env, depth),
            4 => self.gen_lambda_app(env, depth),
            5 => {
                let resume = self.choices.next_mod(2) == 0;
                self.gen_handle(depth, resume, false)
            }
            6 => self.gen_handle(depth, true, true),
            7 => self.gen_fix_app(RecursionTag::Structural, depth),
            8 => self.gen_fix_app(RecursionTag::Measure, depth),
            _ => self.gen_fix_app(RecursionTag::Div, depth),
        }
    }

    fn gen_nat_base(&mut self, env: &Env) -> Term {
        let vars = env.vars_of_type(&Type::Nat);
        if !vars.is_empty() && self.choices.next_mod(3) == 0 {
            return Term::var(&vars[usize::from(self.choices.next()) % vars.len()]);
        }
        let max = usize::from(self.choices.next_mod(4));
        self.gen_pure_nat(max)
    }

    fn gen_pure_nat(&mut self, max: usize) -> Term {
        let n = usize::from(self.choices.next_mod((max.min(5) + 1) as u8));
        Term::nat(n as u64)
    }

    fn gen_let_nat(&mut self, env: &Env, depth: usize) -> Term {
        let var = self.fresh_name("n");
        let expr = self.gen_nat(env, depth.saturating_sub(1));
        let body = self.gen_nat(
            &env.with_var(var.clone(), Type::Nat),
            depth.saturating_sub(1),
        );
        Term::Let {
            var,
            expr: Box::new(expr),
            body: Box::new(body),
        }
    }

    fn gen_case_nat(&mut self, env: &Env, depth: usize) -> Term {
        let succ_var = self.fresh_name("pred");
        let scrutinee = if self.choices.next_mod(3) == 0 {
            self.gen_nat_base(env)
        } else {
            self.gen_nat(env, depth.saturating_sub(1))
        };
        // `case` evaluates exactly one branch (`case-zero`/`case-succ`,
        // `calculus.md §5`).  Until Sprint 03 has a checker/path-sensitive solver, the
        // generator keeps arbitrary `case` branches terminating so the derived
        // divergence witness remains an executable must-diverge fact.
        let zero_body = self.gen_total_nat(env, depth.saturating_sub(1));
        let succ_body = self.gen_total_nat(
            &env.with_var(succ_var.clone(), Type::Nat),
            depth.saturating_sub(1),
        );
        Term::CaseNat {
            scrutinee: Box::new(scrutinee),
            zero_body: Box::new(zero_body),
            succ_var,
            succ_body: Box::new(succ_body),
        }
    }

    fn gen_total_nat(&mut self, env: &Env, depth: usize) -> Term {
        if depth == 0 {
            return self.gen_nat_base(env);
        }
        match self.choices.next_mod(8) {
            0 => self.gen_nat_base(env),
            1 => Term::succ(self.gen_total_nat(env, depth - 1)),
            2 => {
                let var = self.fresh_name("n");
                let expr = self.gen_total_nat(env, depth - 1);
                let body = self.gen_total_nat(&env.with_var(var.clone(), Type::Nat), depth - 1);
                Term::Let {
                    var,
                    expr: Box::new(expr),
                    body: Box::new(body),
                }
            }
            3 => {
                let succ_var = self.fresh_name("pred");
                Term::CaseNat {
                    scrutinee: Box::new(self.gen_total_nat(env, depth - 1)),
                    zero_body: Box::new(self.gen_total_nat(env, depth - 1)),
                    succ_var: succ_var.clone(),
                    succ_body: Box::new(
                        self.gen_total_nat(&env.with_var(succ_var, Type::Nat), depth - 1),
                    ),
                }
            }
            4 => {
                let param = self.fresh_name("arg");
                let body = self.gen_total_nat(&env.with_var(param.clone(), Type::Nat), depth - 1);
                let arg = self.gen_total_nat(env, depth - 1);
                Term::App(
                    Box::new(Term::Lam {
                        param,
                        param_ty: Type::Nat,
                        body: Box::new(body),
                    }),
                    Box::new(arg),
                )
            }
            5 => {
                let resume = self.choices.next_mod(2) == 0;
                self.gen_handle(depth, resume, false)
            }
            6 => self.gen_fix_app(RecursionTag::Structural, depth),
            _ => self.gen_fix_app(RecursionTag::Measure, depth),
        }
    }

    fn gen_scope_spawn_await(&mut self) -> Term {
        // Sequential oracle task forms (`docs/calculus.md §3/§5`): spawn evaluates a
        // closed task, await consumes the handle, and scope owns the task group.
        Term::Mark(
            CoverageTag::Scope,
            Box::new(Term::Scope(Box::new(Term::Let {
                var: "h".into(),
                expr: Box::new(Term::Mark(
                    CoverageTag::Spawn,
                    Box::new(Term::Spawn(Box::new(Term::nat(7)))),
                )),
                body: Box::new(Term::Mark(
                    CoverageTag::Await,
                    Box::new(Term::Await(Box::new(Term::var("h")))),
                )),
            }))),
        )
    }

    fn gen_scope_spawn_dropped_handle(&mut self) -> Term {
        // Un-awaited task handles are affine drops; the enclosing scope joins at exit
        // (`docs/calculus.md §4.5.3/§5`).
        Term::Mark(
            CoverageTag::Scope,
            Box::new(Term::Scope(Box::new(Term::Let {
                var: "h".into(),
                expr: Box::new(Term::Mark(
                    CoverageTag::Spawn,
                    Box::new(Term::Spawn(Box::new(Term::nat(3)))),
                )),
                body: Box::new(Term::zero()),
            }))),
        )
    }

    fn gen_array_inplace(&mut self) -> Term {
        // Arrays and prefix forms from `docs/calculus.md §3.2/§5/§9.2`; the generator
        // exercises the always-copy oracle path for `inplace`, while surface tests enforce q=1.
        Term::Let {
            var: "a".into(),
            expr: Box::new(Term::MkArray(
                Box::new(Term::nat(2)),
                Box::new(Term::nat(0)),
            )),
            body: Box::new(Term::Let {
                var: "b".into(),
                expr: Box::new(Term::Inplace(Box::new(Term::ArraySet(
                    Box::new(Term::var("a")),
                    Box::new(Term::nat(1)),
                    Box::new(Term::nat(7)),
                )))),
                body: Box::new(Term::ArrayGet(
                    Box::new(Term::Freeze(Box::new(Term::var("b")))),
                    Box::new(Term::nat(1)),
                )),
            }),
        }
    }

    fn record_with_buffer(&mut self, value: u64, len: u64) -> Term {
        let buf = Term::MkArray(Box::new(Term::nat(1)), Box::new(Term::nat(value)));
        let empty_record = Term::MkArray(Box::new(Term::nat(2)), Box::new(Term::zero()));
        let with_buf = Term::ArraySet(
            Box::new(empty_record),
            Box::new(Term::zero()),
            Box::new(buf),
        );
        Term::Mark(
            CoverageTag::RecordAggregate,
            Box::new(Term::ArraySet(
                Box::new(with_buf),
                Box::new(Term::nat(1)),
                Box::new(Term::nat(len)),
            )),
        )
    }

    fn gen_record_construct_peek(&mut self) -> Term {
        // Record literals lower to data-region field arrays (`docs/calculus.md §3/§9.2`).
        Term::Let {
            var: "record".into(),
            expr: Box::new(self.record_with_buffer(5, 1)),
            body: Box::new(Term::Mark(
                CoverageTag::DestructureConsume,
                Box::new(Term::ArrayGet(
                    Box::new(Term::ArrayGet(
                        Box::new(Term::var("record")),
                        Box::new(Term::zero()),
                    )),
                    Box::new(Term::zero()),
                )),
            )),
        }
    }

    fn gen_record_functional_update(&mut self) -> Term {
        // Functional record update copies (`docs/calculus.md §5/§9.2`).
        Term::Let {
            var: "record".into(),
            expr: Box::new(self.record_with_buffer(0, 1)),
            body: Box::new(Term::Let {
                var: "updated".into(),
                expr: Box::new(Term::Mark(
                    CoverageTag::RecordFunctionalUpdate,
                    Box::new(Term::ArraySet(
                        Box::new(Term::var("record")),
                        Box::new(Term::nat(1)),
                        Box::new(Term::nat(3)),
                    )),
                )),
                body: Box::new(Term::ArrayGet(
                    Box::new(Term::var("updated")),
                    Box::new(Term::nat(1)),
                )),
            }),
        }
    }

    fn gen_record_inplace_update(&mut self) -> Term {
        // In-place record replacement is the licensed destructive form (`§4.2/§9.2`).
        Term::Let {
            var: "record".into(),
            expr: Box::new(self.record_with_buffer(0, 1)),
            body: Box::new(Term::Let {
                var: "updated".into(),
                expr: Box::new(Term::Mark(
                    CoverageTag::RecordInplaceUpdate,
                    Box::new(Term::Inplace(Box::new(Term::ArraySet(
                        Box::new(Term::var("record")),
                        Box::new(Term::nat(1)),
                        Box::new(Term::nat(4)),
                    )))),
                )),
                body: Box::new(Term::ArrayGet(
                    Box::new(Term::var("updated")),
                    Box::new(Term::nat(1)),
                )),
            }),
        }
    }

    fn gen_destructure_consume_chain(&mut self) -> Term {
        // Destructure-consume transfers unique heap payload ownership out of a dead aggregate
        // (`docs/calculus.md §4.2`); the lowered core is a field load followed by `inplace`.
        Term::Let {
            var: "record".into(),
            expr: Box::new(self.record_with_buffer(0, 1)),
            body: Box::new(Term::Let {
                var: "buf".into(),
                expr: Box::new(Term::Mark(
                    CoverageTag::DestructureConsume,
                    Box::new(Term::ArrayGet(
                        Box::new(Term::var("record")),
                        Box::new(Term::zero()),
                    )),
                )),
                body: Box::new(Term::Let {
                    var: "touched".into(),
                    expr: Box::new(Term::Inplace(Box::new(Term::ArraySet(
                        Box::new(Term::var("buf")),
                        Box::new(Term::zero()),
                        Box::new(Term::nat(9)),
                    )))),
                    body: Box::new(Term::ArrayGet(
                        Box::new(Term::var("touched")),
                        Box::new(Term::zero()),
                    )),
                }),
            }),
        }
    }

    fn list_nil(&mut self) -> Term {
        Term::Mark(
            CoverageTag::VariantAggregate,
            Box::new(Term::MkArray(
                Box::new(Term::nat(3)),
                Box::new(Term::zero()),
            )),
        )
    }

    fn list_cons(&mut self, head: u64, tail: Term) -> Term {
        let base = Term::MkArray(Box::new(Term::nat(3)), Box::new(Term::zero()));
        let with_tag = Term::ArraySet(
            Box::new(base),
            Box::new(Term::zero()),
            Box::new(Term::nat(1)),
        );
        let with_head = Term::ArraySet(
            Box::new(with_tag),
            Box::new(Term::nat(1)),
            Box::new(Term::nat(head)),
        );
        Term::Mark(
            CoverageTag::VariantAggregate,
            Box::new(Term::ArraySet(
                Box::new(with_head),
                Box::new(Term::nat(2)),
                Box::new(tail),
            )),
        )
    }

    fn gen_variant_structural_fold(&mut self) -> Term {
        // Constructor-pattern descent (`docs/calculus.md §4.8/§7`): the recursive call is
        // on the tail payload extracted from the current list value.
        let sum = self.fresh_name("sum");
        let xs = self.fresh_name("xs");
        let is_cons = self.fresh_name("is_cons");
        let tail = self.fresh_name("tail");
        let body = Term::CaseNat {
            scrutinee: Box::new(Term::ArrayGet(
                Box::new(Term::var(&xs)),
                Box::new(Term::zero()),
            )),
            zero_body: Box::new(Term::zero()),
            succ_var: is_cons,
            succ_body: Box::new(Term::Let {
                var: tail.clone(),
                expr: Box::new(Term::Mark(
                    CoverageTag::ConstructorPatternDescent,
                    Box::new(Term::ArrayGet(
                        Box::new(Term::var(&xs)),
                        Box::new(Term::nat(2)),
                    )),
                )),
                body: Box::new(Term::Succ(Box::new(Term::App(
                    Box::new(Term::var(&sum)),
                    Box::new(Term::var(&tail)),
                )))),
            }),
        };
        let nil = self.list_nil();
        let tail = self.list_cons(2, nil);
        let list = self.list_cons(1, tail);
        Term::App(
            Box::new(Term::Fix {
                func: sum,
                param: xs,
                param_ty: Type::Array,
                body: Box::new(body),
                tag: RecursionTag::Structural,
            }),
            Box::new(list),
        )
    }

    fn gen_lambda_app(&mut self, env: &Env, depth: usize) -> Term {
        let param = self.fresh_name("arg");
        let body = self.gen_nat(
            &env.with_var(param.clone(), Type::Nat),
            depth.saturating_sub(1),
        );
        let arg = self.gen_nat(env, depth.saturating_sub(1));
        Term::App(
            Box::new(Term::Lam {
                param,
                param_ty: Type::Nat,
                body: Box::new(body),
            }),
            Box::new(arg),
        )
    }

    fn gen_fix_app(&mut self, tag: RecursionTag, depth: usize) -> Term {
        let func = self.fresh_name("f");
        let param = self.fresh_name("x");
        let body = match tag {
            RecursionTag::Structural => self.structural_fix_body(&func, &param, depth),
            RecursionTag::Measure => self.measure_fix_body(&func, &param),
            RecursionTag::Div => Term::App(
                Box::new(Term::var(func.clone())),
                Box::new(Term::var(param.clone())),
            ),
        };
        let fix = Term::Fix {
            func,
            param,
            param_ty: Type::Nat,
            body: Box::new(body),
            tag,
        };
        let arg_size = if tag == RecursionTag::Div { 0 } else { 3 };
        Term::App(Box::new(fix), Box::new(Term::nat(arg_size)))
    }

    fn structural_fix_body(&mut self, func: &str, param: &str, depth: usize) -> Term {
        let pred = self.fresh_name("pred");
        let rec_call = Term::App(Box::new(Term::var(func)), Box::new(Term::var(&pred)));
        let succ_body = if depth > 1 && self.choices.next_mod(2) == 0 {
            let tmp = self.fresh_name("r");
            Term::Let {
                var: tmp.clone(),
                expr: Box::new(rec_call),
                body: Box::new(Term::var(tmp)),
            }
        } else {
            rec_call
        };
        Term::CaseNat {
            scrutinee: Box::new(Term::var(param)),
            zero_body: Box::new(Term::zero()),
            succ_var: pred,
            succ_body: Box::new(succ_body),
        }
    }

    fn measure_fix_body(&mut self, func: &str, param: &str) -> Term {
        let pred = self.fresh_name("ignored");
        Term::CaseNat {
            scrutinee: Box::new(Term::var(param)),
            zero_body: Box::new(Term::zero()),
            succ_var: pred,
            succ_body: Box::new(Term::App(Box::new(Term::var(func)), Box::new(Term::zero()))),
        }
    }

    fn gen_handle(&mut self, depth: usize, resume: bool, nested: bool) -> Term {
        let body = if nested {
            let inner_var = self.fresh_name("inner");
            let inner = Term::Handle {
                body: Box::new(self.gen_effectful_body(depth.saturating_sub(1))),
                handler: self.gen_handler(true),
            };
            Term::Let {
                var: inner_var,
                expr: Box::new(inner),
                body: Box::new(self.gen_effectful_body(depth.saturating_sub(1))),
            }
        } else {
            self.gen_effectful_body(depth.saturating_sub(1))
        };
        Term::Handle {
            body: Box::new(body),
            handler: self.gen_handler(resume),
        }
    }

    fn gen_effectful_body(&mut self, depth: usize) -> Term {
        let perform = Term::Perform(Label::L, Box::new(self.gen_pure_nat(2)));
        let layers = 1 + usize::from(self.choices.next_mod(3));
        self.wrap_effectful_context(perform, depth, layers)
    }

    fn wrap_effectful_context(&mut self, inner: Term, depth: usize, layers: usize) -> Term {
        if layers == 0 || depth == 0 {
            return inner;
        }
        let wrapped = match self.choices.next_mod(4) {
            0 => {
                let var = self.fresh_name("cap");
                Term::Let {
                    var: var.clone(),
                    expr: Box::new(inner),
                    body: Box::new(Term::var(var)),
                }
            }
            1 => Term::App(
                Box::new(Term::Lam {
                    param: "z".into(),
                    param_ty: Type::Nat,
                    body: Box::new(Term::var("z")),
                }),
                Box::new(inner),
            ),
            2 => Term::CaseNat {
                scrutinee: Box::new(inner),
                zero_body: Box::new(Term::zero()),
                succ_var: "case_pred".into(),
                succ_body: Box::new(Term::var("case_pred")),
            },
            _ => Term::Succ(Box::new(inner)),
        };
        self.wrap_effectful_context(wrapped, depth - 1, layers - 1)
    }

    fn gen_multi_label_transparent(&mut self) -> Term {
        let label_a = Label::intern("A");
        let label_b = Label::intern("B");
        let inner = Handler::single(
            "r".into(),
            Box::new(Term::var("r")),
            OpClause {
                op_label: label_a,
                op_param: "p".into(),
                op_k: "k".into(),
                op_body: Box::new(Term::Resume {
                    kont: Box::new(Term::var("k")),
                    arg: Box::new(Term::var("p")),
                }),
            },
        );
        let outer = Handler::single(
            "r".into(),
            Box::new(Term::var("r")),
            OpClause {
                op_label: label_b,
                op_param: "p".into(),
                op_k: "_k".into(),
                op_body: Box::new(Term::nat(8)),
            },
        );
        Term::Handle {
            body: Box::new(Term::Handle {
                body: Box::new(Term::Perform(label_b, Box::new(self.gen_pure_nat(1)))),
                handler: inner,
            }),
            handler: outer,
        }
    }

    fn gen_multi_label_clause_set(&mut self) -> Term {
        let label_a = Label::intern("A");
        let label_b = Label::intern("B");
        Term::Handle {
            body: Box::new(Term::Perform(label_a, Box::new(self.gen_pure_nat(2)))),
            handler: Handler {
                return_var: "r".into(),
                return_body: Box::new(Term::var("r")),
                clauses: vec![
                    OpClause {
                        op_label: label_a,
                        op_param: "p".into(),
                        op_k: "k".into(),
                        op_body: Box::new(Term::Resume {
                            kont: Box::new(Term::var("k")),
                            arg: Box::new(Term::var("p")),
                        }),
                    },
                    OpClause {
                        op_label: label_b,
                        op_param: "q".into(),
                        op_k: "_k".into(),
                        op_body: Box::new(Term::var("q")),
                    },
                ],
            },
        }
    }

    fn gen_fix_group(&mut self, tag: RecursionTag) -> Term {
        // Generated `fix*` groups (`calculus.md §3/§4.8/§7.1`) provide natural
        // multi-node SCCs for the boundedness solver, closing Sprint 03's singleton-SCC
        // coverage reservation.
        let even = self.fresh_name("even");
        let odd = self.fresh_name("odd");
        let n_even = self.fresh_name("n");
        let n_odd = self.fresh_name("n");
        let p_even = self.fresh_name("p");
        let p_odd = self.fresh_name("p");
        let even_body = Term::CaseNat {
            scrutinee: Box::new(Term::var(&n_even)),
            zero_body: Box::new(Term::nat(1)),
            succ_var: p_even.clone(),
            succ_body: Box::new(Term::App(
                Box::new(Term::var(&odd)),
                Box::new(Term::var(&p_even)),
            )),
        };
        let odd_body = Term::CaseNat {
            scrutinee: Box::new(Term::var(&n_odd)),
            zero_body: Box::new(Term::zero()),
            succ_var: p_odd.clone(),
            succ_body: Box::new(Term::App(
                Box::new(Term::var(&even)),
                Box::new(Term::var(&p_odd)),
            )),
        };
        Term::App(
            Box::new(Term::FixGroup {
                bindings: vec![
                    FixBinding {
                        func: even.clone(),
                        param: n_even,
                        param_ty: Type::Nat,
                        body: Box::new(even_body),
                        tag,
                    },
                    FixBinding {
                        func: odd,
                        param: n_odd,
                        param_ty: Type::Nat,
                        body: Box::new(odd_body),
                        tag,
                    },
                ],
                entry: even,
            }),
            Box::new(Term::nat(4)),
        )
    }

    fn gen_handler(&mut self, resume: bool) -> Handler {
        let op_body = if resume {
            let resume = Term::Resume {
                kont: Box::new(Term::var("k")),
                arg: Box::new(Term::var("p")),
            };
            if self.choices.next_mod(2) == 0 {
                resume
            } else {
                Term::Let {
                    var: "resumed".into(),
                    expr: Box::new(resume),
                    body: Box::new(Term::var("resumed")),
                }
            }
        } else {
            Term::var("p")
        };
        Handler::single(
            "r".into(),
            Box::new(Term::var("r")),
            OpClause {
                op_label: Label::L,
                op_param: "p".into(),
                op_k: "k".into(),
                op_body: Box::new(op_body),
            },
        )
    }
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: Vec<(String, Type)>,
    cont_vars: BTreeSet<String>,
    rec: Option<RecContext>,
    recs: Vec<RecContext>,
}

impl Env {
    fn with_var(&self, name: String, ty: Type) -> Self {
        let mut next = self.clone();
        next.vars.push((name, ty));
        next
    }

    fn with_cont(&self, name: &str) -> Self {
        let mut next = self.with_var(
            name.into(),
            Type::Cont(Box::new(Type::Nat), Box::new(Type::Nat)),
        );
        next.cont_vars.insert(name.into());
        next
    }

    fn vars_of_type(&self, ty: &Type) -> Vec<String> {
        self.vars
            .iter()
            .filter(|(_, found)| found == ty)
            .map(|(name, _)| name.clone())
            .collect()
    }

    fn lookup(&self, name: &str) -> Option<Type> {
        self.vars
            .iter()
            .rev()
            .find(|(found, _)| found == name)
            .map(|(_, ty)| ty.clone())
    }

    fn with_rec(&self, rec: RecContext) -> Self {
        let mut next = self.clone();
        next.vars.push((
            rec.func.clone(),
            Type::Arrow(Box::new(Type::Nat), Box::new(Type::Nat)),
        ));
        next.vars.push((rec.param.clone(), Type::Nat));
        next.recs = vec![rec.clone()];
        next.rec = Some(rec);
        next
    }

    fn with_rec_group(&self, recs: Vec<RecContext>, current_func: &str, param: &str) -> Self {
        let mut next = self.clone();
        for rec in &recs {
            next.vars.push((
                rec.func.clone(),
                Type::Arrow(Box::new(Type::Nat), Box::new(Type::Nat)),
            ));
        }
        next.vars.push((param.into(), Type::Nat));
        next.rec = recs.iter().find(|rec| rec.func == current_func).cloned();
        next.recs = recs;
        next
    }

    fn with_strict_var(&self, strict_var: &str) -> Self {
        let mut next = self.clone();
        if let Some(rec) = &mut next.rec {
            rec.strict_var = Some(strict_var.into());
            for group_rec in &mut next.recs {
                if group_rec.func == rec.func {
                    group_rec.strict_var = Some(strict_var.into());
                }
            }
        }
        next
    }
}

#[derive(Debug, Clone)]
struct RecContext {
    func: String,
    param: String,
    tag: RecursionTag,
    strict_var: Option<String>,
}

#[derive(Debug, Clone)]
struct Derived {
    ty: Type,
    effects: Eff,
    bound: Bound,
    region: Region,
    continuation_uses: ContinuationUseFacts,
    divergence: Divergence,
    coverage: BTreeSet<CoverageTag>,
}

impl Derived {
    fn pure(ty: Type) -> Self {
        Self {
            ty,
            effects: Eff::empty(),
            bound: Bound::ZERO,
            region: Region::Arena,
            continuation_uses: ContinuationUseFacts {
                introduced: 0,
                resumed: 0,
                dropped: 0,
            },
            divergence: Divergence::Terminates,
            coverage: BTreeSet::new(),
        }
    }

    fn into_witness(self) -> Witness {
        Witness {
            ty: self.ty,
            effects: self.effects,
            bound: self.bound,
            region: self.region,
            continuation_uses: self.continuation_uses,
            divergence: self.divergence,
            coverage: self.coverage,
        }
    }

    fn combine(mut self, rhs: &Self) -> Self {
        self.effects = self.effects.join(&rhs.effects);
        self.bound = self.bound.sequential(rhs.bound);
        self.region = self.region.meet(rhs.region);
        self.continuation_uses.introduced += rhs.continuation_uses.introduced;
        self.continuation_uses.resumed += rhs.continuation_uses.resumed;
        self.continuation_uses.dropped += rhs.continuation_uses.dropped;
        if rhs.divergence == Divergence::Div {
            self.divergence = Divergence::Div;
        }
        self.coverage.extend(rhs.coverage.iter().copied());
        self
    }
}

fn contextualize(effectful_child: &Derived) -> Bound {
    if !effectful_child.effects.is_empty() {
        effectful_child.bound.sequential(Bound::finite(1))
    } else {
        effectful_child.bound
    }
}

fn type_compatible(found: &Type, expected: &Type) -> bool {
    found == expected
        || matches!(
            (found, expected),
            (Type::Nat, Type::Array) | (Type::Array, Type::Nat)
        )
}

fn derive(term: &Term, env: &Env) -> Derived {
    match term {
        Term::Unit => Derived::pure(Type::Unit),
        Term::Zero => Derived::pure(Type::Nat),
        Term::Array(_) => Derived::pure(Type::Array),
        Term::Succ(inner) => {
            let inner = derive(inner, env);
            debug_assert_eq!(inner.ty, Type::Nat);
            let mut out = inner;
            out.ty = Type::Nat;
            out.bound = contextualize(&out);
            out
        }
        Term::MkArray(len, fill) => {
            let len_d = derive(len, env);
            let fill_d = derive(fill, env);
            let mut out = len_d.combine(&fill_d);
            out.ty = Type::Array;
            out.coverage.insert(CoverageTag::Array);
            out
        }
        Term::ArrayGet(array, index) => {
            let array_d = derive(array, env);
            let index_d = derive(index, env);
            let mut out = array_d.combine(&index_d);
            out.ty = Type::Nat;
            out.coverage.insert(CoverageTag::Array);
            out
        }
        Term::ArraySet(array, index, value) => {
            let array_d = derive(array, env);
            let index_d = derive(index, env);
            let value_d = derive(value, env);
            let mut out = array_d.combine(&index_d).combine(&value_d);
            out.ty = Type::Array;
            out.coverage.insert(CoverageTag::Array);
            out
        }
        Term::ArrayLen(array) => {
            let mut out = derive(array, env);
            out.ty = Type::Nat;
            out.coverage.insert(CoverageTag::Array);
            out
        }
        Term::Move(inner) | Term::Inplace(inner) | Term::Freeze(inner) => {
            let mut out = derive(inner, env);
            out.coverage.insert(CoverageTag::Array);
            out
        }
        Term::Mark(tag, inner) => {
            let mut out = derive(inner, env);
            out.coverage.insert(*tag);
            out
        }
        Term::Scope(inner) => {
            let mut out = derive(inner, env);
            out.coverage.insert(CoverageTag::Scope);
            out
        }
        Term::Spawn(inner) => {
            let mut out = derive(inner, env);
            debug_assert!(
                out.effects.is_empty(),
                "spawned generated term must be pure"
            );
            out.ty = Type::Task(Box::new(out.ty));
            out.coverage.insert(CoverageTag::Spawn);
            out
        }
        Term::Await(inner) => {
            let mut out = derive(inner, env);
            out.coverage.insert(CoverageTag::Await);
            if let Type::Task(result) = out.ty.clone() {
                out.ty = *result;
            }
            out
        }
        Term::TaskValue(inner) => {
            let inner = derive(inner, env);
            Derived::pure(Type::Task(Box::new(inner.ty)))
        }
        Term::Var(name) => Derived::pure(env.lookup(name).unwrap_or(Type::Nat)),
        Term::Lam {
            param,
            param_ty,
            body,
        } => {
            let body = derive(body, &env.with_var(param.clone(), param_ty.clone()));
            Derived::pure(Type::Arrow(Box::new(param_ty.clone()), Box::new(body.ty)))
        }
        Term::App(fun, arg) => derive_app(fun, arg, env),
        Term::Let { var, expr, body } => {
            let expr_d = derive(expr, env);
            let body_d = derive(body, &env.with_var(var.clone(), expr_d.ty.clone()));
            let result_ty = body_d.ty.clone();
            let expr_bound = contextualize(&expr_d);
            let mut out = expr_d.combine(&body_d);
            out.ty = result_ty;
            out.bound = expr_bound.sequential(body_d.bound);
            out.coverage.insert(CoverageTag::Let);
            out
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            let scrut_d = derive(scrutinee, env);
            let zero_d = derive(zero_body, env);
            let succ_env = env.with_var(succ_var.clone(), Type::Nat);
            let succ_env = if matches!(&**scrutinee, Term::Var(name) if env.rec.as_ref().is_some_and(|rec| rec.param == *name))
            {
                succ_env.with_strict_var(succ_var)
            } else {
                succ_env
            };
            let succ_d = derive(succ_body, &succ_env);
            debug_assert_eq!(scrut_d.ty, Type::Nat);
            debug_assert_eq!(zero_d.ty, succ_d.ty);
            let scrut_bound = contextualize(&scrut_d);
            let result_ty = zero_d.ty.clone();
            let branch_bound = zero_d.bound.join(succ_d.bound);
            let divergence = case_divergence(scrutinee, &scrut_d, &zero_d, &succ_d);
            let mut out = scrut_d.combine(&zero_d).combine(&succ_d);
            out.ty = result_ty;
            out.bound = scrut_bound.sequential(branch_bound);
            // `case-zero` / `case-succ` (`calculus.md §5`) evaluate exactly one branch.
            // Divergence is therefore a must-diverge fact for the executed path, not the
            // join of both branch possibilities.
            out.divergence = divergence;
            out
        }
        Term::Fix {
            func,
            param,
            param_ty,
            body,
            tag,
        } => {
            debug_assert!(
                type_compatible(param_ty, &Type::Nat),
                "fix parameter must be Nat-compatible"
            );
            let rec = RecContext {
                func: func.clone(),
                param: param.clone(),
                tag: *tag,
                strict_var: None,
            };
            let body_d = derive(body, &env.with_rec(rec));
            let mut out = Derived::pure(Type::Arrow(Box::new(Type::Nat), Box::new(body_d.ty)));
            out.coverage = body_d.coverage;
            out.bound = match tag {
                RecursionTag::Structural => body_d.bound,
                RecursionTag::Measure => body_d.bound.join(Bound::finite(1)),
                RecursionTag::Div => Bound::Omega,
            };
            out.divergence = if out.bound == Bound::Omega {
                Divergence::Div
            } else {
                body_d.divergence
            };
            match tag {
                RecursionTag::Structural => {
                    out.coverage.insert(CoverageTag::FixStructural);
                }
                RecursionTag::Measure => {
                    out.coverage.insert(CoverageTag::FixMeasure);
                }
                RecursionTag::Div => {}
            }
            out
        }
        Term::FixGroup { bindings, entry } => derive_fix_group(bindings, entry, env),
        Term::Perform(label, arg) => {
            let arg_d = derive(arg, env);
            debug_assert_eq!(arg_d.ty, Type::Nat);
            let mut out = arg_d;
            out.ty = Type::Nat;
            out.effects = out.effects.join(&Eff::singleton(*label));
            // Sprint 02's executable frame metric charges captured context frames, not the
            // operation redex itself; see SPEC-GAP(frame-metric-byte-accuracy).
            out.coverage.insert(CoverageTag::Perform);
            out
        }
        Term::Handle { body, handler } => derive_handle(body, handler, env),
        Term::Resume { kont, arg } => {
            let arg_d = derive(arg, env);
            let kont_resumes = matches!(&**kont, Term::Var(name) if env.cont_vars.contains(name));
            let mut out = arg_d;
            out.ty = Type::Nat;
            if kont_resumes {
                out.continuation_uses.resumed += 1;
            }
            out
        }
        Term::Cont(_) => Derived::pure(Type::Cont(Box::new(Type::Nat), Box::new(Type::Nat))),
    }
}

fn case_divergence(
    scrutinee: &Term,
    scrut_d: &Derived,
    zero_d: &Derived,
    succ_d: &Derived,
) -> Divergence {
    if scrut_d.divergence == Divergence::Div {
        return Divergence::Div;
    }
    match scrutinee {
        Term::Zero => zero_d.divergence,
        Term::Succ(_) => succ_d.divergence,
        _ if zero_d.divergence == Divergence::Div && succ_d.divergence == Divergence::Div => {
            Divergence::Div
        }
        _ => Divergence::Terminates,
    }
}

fn derive_app(fun: &Term, arg: &Term, env: &Env) -> Derived {
    if let Term::Var(func) = fun {
        if let Some(rec) = env.recs.iter().find(|rec| rec.func == *func) {
            let arg_d = derive(arg, env);
            let strict = matches!(arg, Term::Var(name) if rec.strict_var.as_ref() == Some(name))
                || matches!(
                    (arg, env.rec.as_ref()),
                    (Term::Var(name), Some(current)) if current.func == rec.func && name != &current.param
                );
            let mut out = arg_d;
            out.ty = Type::Nat;
            out.bound = match rec.tag {
                RecursionTag::Structural
                    if strict
                        && env
                            .rec
                            .as_ref()
                            .is_some_and(|current| current.func == rec.func) =>
                {
                    Bound::finite(1)
                }
                RecursionTag::Structural => Bound::Omega,
                RecursionTag::Measure => Bound::finite(1),
                RecursionTag::Div => Bound::Omega,
            };
            if out.bound == Bound::Omega {
                out.divergence = Divergence::Div;
            }
            return out;
        }
    }

    if let Term::Lam {
        param,
        param_ty,
        body,
    } = fun
    {
        let arg_d = derive(arg, env);
        let body_d = derive(body, &env.with_var(param.clone(), param_ty.clone()));
        let result_ty = body_d.ty.clone();
        let arg_bound = contextualize(&arg_d);
        let mut out = arg_d.combine(&body_d);
        out.ty = result_ty;
        out.bound = arg_bound.sequential(body_d.bound);
        out.coverage.insert(CoverageTag::LambdaApp);
        return out;
    }

    let fun_d = derive(fun, env);
    let arg_d = derive(arg, env);
    let result_ty = match &fun_d.ty {
        Type::Arrow(_, ret) => (**ret).clone(),
        _ => Type::Nat,
    };
    let fun_bound = contextualize(&fun_d);
    let arg_bound = contextualize(&arg_d);
    let mut out = fun_d.combine(&arg_d);
    out.ty = result_ty;
    out.bound = fun_bound.sequential(arg_bound);
    out
}

fn derive_fix_group(bindings: &[FixBinding], entry: &str, env: &Env) -> Derived {
    // Compositional analyzer mirror of group typing (`calculus.md §4.8`): all members are
    // in scope for all bodies, and the selected entry determines the arrow witness.
    let recs: Vec<_> = bindings
        .iter()
        .map(|binding| RecContext {
            func: binding.func.clone(),
            param: binding.param.clone(),
            tag: binding.tag,
            strict_var: None,
        })
        .collect();
    let mut body_results = BTreeMap::new();
    let mut coverage = BTreeSet::new();
    for binding in bindings {
        debug_assert!(
            type_compatible(&binding.param_ty, &Type::Nat),
            "fix* parameter must be Nat-compatible"
        );
        let body_d = derive(
            &binding.body,
            &env.with_rec_group(recs.clone(), &binding.func, &binding.param),
        );
        coverage.extend(body_d.coverage.iter().copied());
        match binding.tag {
            RecursionTag::Structural => {
                coverage.insert(CoverageTag::FixStructural);
            }
            RecursionTag::Measure => {
                coverage.insert(CoverageTag::FixMeasure);
            }
            RecursionTag::Div => {}
        }
        body_results.insert(binding.func.clone(), body_d);
    }
    let entry_binding = bindings
        .iter()
        .find(|binding| binding.func == entry)
        .or_else(|| bindings.first());
    let Some(entry_binding) = entry_binding else {
        return Derived::pure(Type::Arrow(Box::new(Type::Nat), Box::new(Type::Nat)));
    };
    let entry_body = body_results
        .get(&entry_binding.func)
        .cloned()
        .unwrap_or_else(|| Derived::pure(Type::Nat));
    let mut out = Derived::pure(Type::Arrow(
        Box::new(Type::Nat),
        Box::new(entry_body.ty.clone()),
    ));
    out.coverage = coverage;
    out.bound = match entry_binding.tag {
        RecursionTag::Structural => entry_body.bound,
        RecursionTag::Measure => entry_body.bound.join(Bound::finite(1)),
        RecursionTag::Div => Bound::Omega,
    };
    out.divergence = if out.bound == Bound::Omega {
        Divergence::Div
    } else {
        entry_body.divergence
    };
    out
}

fn derive_handle(body: &Term, handler: &Handler, env: &Env) -> Derived {
    let body_d = derive(body, env);
    let ret_d = derive(
        &handler.return_body,
        &env.with_var(handler.return_var.clone(), body_d.ty.clone()),
    );
    let mut handled_effects = body_d.effects.clone();
    let mut op_effects = Eff::empty();
    let mut op_bound = Bound::ZERO;
    let mut op_region = Region::Arena;
    let mut introduced = 0;
    let mut resumes = 0;
    let mut op_diverges = false;
    let mut op_coverage = BTreeSet::new();
    for clause in &handler.clauses {
        let op_env = env
            .with_var(clause.op_param.clone(), Type::Nat)
            .with_cont(&clause.op_k);
        let op_d = derive(&clause.op_body, &op_env);
        let clause_introduced = u32::from(body_d.effects.contains(clause.op_label));
        let clause_resumes = op_d.continuation_uses.resumed;
        introduced += clause_introduced;
        resumes += clause_resumes;
        let effective = if clause_resumes > 0 {
            // Lazy `H-op-resume` (`calculus.md §5`) materializes the deep one-shot
            // continuation, so the `Handle` rule (`§4.7`) adds the carried body `β`.
            op_d.bound.sequential(body_d.bound)
        } else {
            // Lazy `H-op-drop` does not materialize `k`; dropped exception/default clauses
            // keep `β̂ᵢ = βᵢ` (`calculus.md §4.7`).
            op_d.bound
        };
        op_bound = op_bound.join(effective);
        op_region = op_region.meet(op_d.region);
        op_effects = op_effects.join(&op_d.effects);
        op_diverges |= op_d.divergence == Divergence::Div;
        op_coverage.extend(op_d.coverage.iter().copied());
        op_coverage.insert(if clause_resumes > 0 {
            CoverageTag::HandleResuming
        } else {
            CoverageTag::HandleDropped
        });
        handled_effects = handled_effects.without(clause.op_label);
    }
    let mut out = Derived::pure(ret_d.ty.clone());
    out.effects = handled_effects.join(&ret_d.effects).join(&op_effects);
    out.bound = ret_d.bound.join(op_bound);
    out.region = body_d.region.meet(ret_d.region).meet(op_region);
    out.continuation_uses = ContinuationUseFacts {
        introduced,
        resumed: resumes,
        dropped: introduced.saturating_sub(resumes),
    };
    out.divergence = if body_d.divergence == Divergence::Div
        || ret_d.divergence == Divergence::Div
        || op_diverges
    {
        Divergence::Div
    } else {
        Divergence::Terminates
    };
    out.coverage = body_d.coverage;
    out.coverage.extend(ret_d.coverage.iter().copied());
    out.coverage.extend(op_coverage);
    out
}

fn analyze_facts(term: &Term) -> GenerationFacts {
    let mut facts = GenerationFacts {
        depth: term_depth(term),
        ..GenerationFacts::default()
    };
    scan_handlers(term, false, &mut facts);
    scan_rec_calls(term, &mut Vec::new(), &mut facts);
    facts
}

fn term_depth(term: &Term) -> usize {
    match term {
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => 1,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => 1 + term_depth(inner),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            1 + term_depth(lhs).max(term_depth(rhs))
        }
        Term::ArraySet(array, index, value) => {
            1 + term_depth(array).max(term_depth(index).max(term_depth(value)))
        }
        Term::Lam { body, .. } | Term::Fix { body, .. } => 1 + term_depth(body),
        Term::FixGroup { bindings, .. } => {
            1 + bindings
                .iter()
                .map(|binding| term_depth(&binding.body))
                .max()
                .unwrap_or(0)
        }
        Term::App(fun, arg) => 1 + term_depth(fun).max(term_depth(arg)),
        Term::Let { expr, body, .. } => 1 + term_depth(expr).max(term_depth(body)),
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_body,
            ..
        } => 1 + term_depth(scrutinee).max(term_depth(zero_body).max(term_depth(succ_body))),
        Term::Handle { body, handler } => {
            1 + handler
                .clauses
                .iter()
                .map(|clause| term_depth(&clause.op_body))
                .fold(
                    term_depth(body).max(term_depth(&handler.return_body)),
                    usize::max,
                )
        }
        Term::Resume { kont, arg } => 1 + term_depth(kont).max(term_depth(arg)),
    }
}

fn scan_handlers(term: &Term, in_handler: bool, facts: &mut GenerationFacts) {
    match term {
        Term::Handle { body, handler } => {
            if in_handler {
                facts.nested_handlers = true;
            }
            scan_handlers(body, true, facts);
            scan_handlers(&handler.return_body, true, facts);
            for clause in &handler.clauses {
                scan_handlers(&clause.op_body, true, facts);
            }
        }
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => scan_handlers(inner, in_handler, facts),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            scan_handlers(lhs, in_handler, facts);
            scan_handlers(rhs, in_handler, facts);
        }
        Term::ArraySet(array, index, value) => {
            scan_handlers(array, in_handler, facts);
            scan_handlers(index, in_handler, facts);
            scan_handlers(value, in_handler, facts);
        }
        Term::Lam { body, .. } | Term::Fix { body, .. } => scan_handlers(body, in_handler, facts),
        Term::FixGroup { bindings, .. } => {
            for binding in bindings {
                scan_handlers(&binding.body, in_handler, facts);
            }
        }
        Term::App(fun, arg) => {
            scan_handlers(fun, in_handler, facts);
            scan_handlers(arg, in_handler, facts);
        }
        Term::Let { expr, body, .. } => {
            scan_handlers(expr, in_handler, facts);
            scan_handlers(body, in_handler, facts);
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_body,
            ..
        } => {
            scan_handlers(scrutinee, in_handler, facts);
            scan_handlers(zero_body, in_handler, facts);
            scan_handlers(succ_body, in_handler, facts);
        }
        Term::Resume { kont, arg } => {
            scan_handlers(kont, in_handler, facts);
            scan_handlers(arg, in_handler, facts);
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => {}
    }
}

#[derive(Debug, Clone)]
struct RecScan {
    func: String,
    param: String,
    strict_vars: BTreeSet<String>,
}

fn scan_rec_calls(term: &Term, stack: &mut Vec<RecScan>, facts: &mut GenerationFacts) {
    match term {
        Term::Fix {
            func, param, body, ..
        } => {
            stack.push(RecScan {
                func: func.clone(),
                param: param.clone(),
                strict_vars: BTreeSet::new(),
            });
            scan_rec_calls(body, stack, facts);
            stack.pop();
        }
        Term::FixGroup { bindings, .. } => {
            let start = stack.len();
            for binding in bindings {
                stack.push(RecScan {
                    func: binding.func.clone(),
                    param: binding.param.clone(),
                    strict_vars: BTreeSet::new(),
                });
            }
            for binding in bindings {
                scan_rec_calls(&binding.body, stack, facts);
            }
            stack.truncate(start);
        }
        Term::App(fun, arg) => {
            if let Term::Var(func) = &**fun {
                if let Some(rec) = stack.iter().rev().find(|rec| rec.func == *func) {
                    let strict = matches!(&**arg, Term::Var(arg_name) if rec.strict_vars.contains(arg_name))
                        || matches!(
                            &**arg,
                            Term::Var(arg_name) if stack
                                .iter()
                                .rev()
                                .find(|current| current.func == rec.func)
                                .is_some_and(|current| arg_name != &current.param)
                        );
                    if strict {
                        facts.strict_rec_calls += 1;
                    } else {
                        facts.non_strict_rec_calls += 1;
                    }
                }
            }
            scan_rec_calls(fun, stack, facts);
            scan_rec_calls(arg, stack, facts);
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            scan_rec_calls(scrutinee, stack, facts);
            scan_rec_calls(zero_body, stack, facts);
            let added_to = if let Term::Var(name) = &**scrutinee {
                stack
                    .iter()
                    .rposition(|rec| rec.param == *name)
                    .inspect(|idx| {
                        stack[*idx].strict_vars.insert(succ_var.clone());
                    })
            } else {
                None
            };
            scan_rec_calls(succ_body, stack, facts);
            if let Some(idx) = added_to {
                stack[idx].strict_vars.remove(succ_var);
            }
        }
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => scan_rec_calls(inner, stack, facts),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            scan_rec_calls(lhs, stack, facts);
            scan_rec_calls(rhs, stack, facts);
        }
        Term::ArraySet(array, index, value) => {
            scan_rec_calls(array, stack, facts);
            scan_rec_calls(index, stack, facts);
            scan_rec_calls(value, stack, facts);
        }
        Term::Lam { body, .. } => scan_rec_calls(body, stack, facts),
        Term::Let { expr, body, .. } => {
            scan_rec_calls(expr, stack, facts);
            scan_rec_calls(body, stack, facts);
        }
        Term::Handle { body, handler } => {
            scan_rec_calls(body, stack, facts);
            scan_rec_calls(&handler.return_body, stack, facts);
            for clause in &handler.clauses {
                scan_rec_calls(&clause.op_body, stack, facts);
            }
        }
        Term::Resume { kont, arg } => {
            scan_rec_calls(kont, stack, facts);
            scan_rec_calls(arg, stack, facts);
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => {}
    }
}

fn is_closed(term: &Term) -> bool {
    let mut scope = Vec::new();
    closed_under(term, &mut scope)
}

fn term_obeys_continuation_usage_under(term: &Term) -> bool {
    match term {
        Term::Handle { body, handler } => {
            term_obeys_continuation_usage_under(body)
                && term_obeys_continuation_usage_under(&handler.return_body)
                && handler.clauses.iter().all(|clause| {
                    term_obeys_continuation_usage_under(&clause.op_body)
                        && handler_clause_obeys_k_usage(&clause.op_body, &clause.op_k)
                })
        }
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => term_obeys_continuation_usage_under(inner),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            term_obeys_continuation_usage_under(lhs) && term_obeys_continuation_usage_under(rhs)
        }
        Term::ArraySet(array, index, value) => {
            term_obeys_continuation_usage_under(array)
                && term_obeys_continuation_usage_under(index)
                && term_obeys_continuation_usage_under(value)
        }
        Term::Lam { body, .. } | Term::Fix { body, .. } => {
            term_obeys_continuation_usage_under(body)
        }
        Term::FixGroup { bindings, .. } => bindings
            .iter()
            .all(|binding| term_obeys_continuation_usage_under(&binding.body)),
        Term::App(fun, arg) | Term::Resume { kont: fun, arg } => {
            term_obeys_continuation_usage_under(fun) && term_obeys_continuation_usage_under(arg)
        }
        Term::Let { expr, body, .. } => {
            term_obeys_continuation_usage_under(expr) && term_obeys_continuation_usage_under(body)
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_body,
            ..
        } => {
            term_obeys_continuation_usage_under(scrutinee)
                && term_obeys_continuation_usage_under(zero_body)
                && term_obeys_continuation_usage_under(succ_body)
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => true,
    }
}

fn handler_clause_obeys_k_usage(clause: &Term, k: &str) -> bool {
    let mentions = free_var_count(clause, k);
    if mentions == 0 {
        return true;
    }
    mentions == 1 && direct_resume_count(clause, k) == 1
}

fn free_var_count(term: &Term, name: &str) -> usize {
    match term {
        Term::Var(var) => usize::from(var == name),
        Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => 0,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => free_var_count(inner, name),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            free_var_count(lhs, name) + free_var_count(rhs, name)
        }
        Term::ArraySet(array, index, value) => {
            free_var_count(array, name) + free_var_count(index, name) + free_var_count(value, name)
        }
        Term::Lam { param, body, .. } => usize::from(param != name) * free_var_count(body, name),
        Term::App(fun, arg) | Term::Resume { kont: fun, arg } => {
            free_var_count(fun, name) + free_var_count(arg, name)
        }
        Term::Let { var, expr, body } => {
            free_var_count(expr, name) + usize::from(var != name) * free_var_count(body, name)
        }
        Term::Fix {
            func, param, body, ..
        } => usize::from(func != name && param != name) * free_var_count(body, name),
        Term::FixGroup { bindings, .. } => {
            if bindings.iter().any(|binding| binding.func == name) {
                0
            } else {
                bindings
                    .iter()
                    .map(|binding| {
                        usize::from(binding.param != name) * free_var_count(&binding.body, name)
                    })
                    .sum()
            }
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            free_var_count(scrutinee, name)
                + free_var_count(zero_body, name)
                + usize::from(succ_var != name) * free_var_count(succ_body, name)
        }
        Term::Handle { body, handler } => {
            free_var_count(body, name)
                + usize::from(handler.return_var != name)
                    * free_var_count(&handler.return_body, name)
                + handler
                    .clauses
                    .iter()
                    .map(|clause| {
                        usize::from(clause.op_param != name && clause.op_k != name)
                            * free_var_count(&clause.op_body, name)
                    })
                    .sum::<usize>()
        }
    }
}

fn direct_resume_count(term: &Term, name: &str) -> usize {
    match term {
        Term::Resume { kont, arg } => {
            let here = usize::from(matches!(&**kont, Term::Var(var) if var == name));
            let kont_nested = if here == 0 {
                direct_resume_count(kont, name)
            } else {
                0
            };
            here + kont_nested + direct_resume_count(arg, name)
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => 0,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => direct_resume_count(inner, name),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            direct_resume_count(lhs, name) + direct_resume_count(rhs, name)
        }
        Term::ArraySet(array, index, value) => {
            direct_resume_count(array, name)
                + direct_resume_count(index, name)
                + direct_resume_count(value, name)
        }
        Term::Lam { param, body, .. } => {
            usize::from(param != name) * direct_resume_count(body, name)
        }
        Term::App(fun, arg) => direct_resume_count(fun, name) + direct_resume_count(arg, name),
        Term::Let { var, expr, body } => {
            direct_resume_count(expr, name)
                + usize::from(var != name) * direct_resume_count(body, name)
        }
        Term::Fix {
            func, param, body, ..
        } => usize::from(func != name && param != name) * direct_resume_count(body, name),
        Term::FixGroup { bindings, .. } => {
            if bindings.iter().any(|binding| binding.func == name) {
                0
            } else {
                bindings
                    .iter()
                    .map(|binding| {
                        usize::from(binding.param != name)
                            * direct_resume_count(&binding.body, name)
                    })
                    .sum()
            }
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            direct_resume_count(scrutinee, name)
                + direct_resume_count(zero_body, name)
                + usize::from(succ_var != name) * direct_resume_count(succ_body, name)
        }
        Term::Handle { body, handler } => {
            direct_resume_count(body, name)
                + usize::from(handler.return_var != name)
                    * direct_resume_count(&handler.return_body, name)
                + handler
                    .clauses
                    .iter()
                    .map(|clause| {
                        usize::from(clause.op_param != name && clause.op_k != name)
                            * direct_resume_count(&clause.op_body, name)
                    })
                    .sum::<usize>()
        }
    }
}

fn closed_under(term: &Term, scope: &mut Vec<String>) -> bool {
    match term {
        Term::Var(name) => scope.contains(name),
        Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => true,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner)
        | Term::Scope(inner)
        | Term::Spawn(inner)
        | Term::Await(inner)
        | Term::TaskValue(inner) => closed_under(inner, scope),
        Term::MkArray(lhs, rhs) | Term::ArrayGet(lhs, rhs) => {
            closed_under(lhs, scope) && closed_under(rhs, scope)
        }
        Term::ArraySet(array, index, value) => {
            closed_under(array, scope) && closed_under(index, scope) && closed_under(value, scope)
        }
        Term::Lam { param, body, .. } => {
            scope.push(param.clone());
            let ok = closed_under(body, scope);
            scope.pop();
            ok
        }
        Term::App(fun, arg) => closed_under(fun, scope) && closed_under(arg, scope),
        Term::Let { var, expr, body } => {
            let expr_ok = closed_under(expr, scope);
            scope.push(var.clone());
            let body_ok = closed_under(body, scope);
            scope.pop();
            expr_ok && body_ok
        }
        Term::Fix {
            func, param, body, ..
        } => {
            scope.push(func.clone());
            scope.push(param.clone());
            let ok = closed_under(body, scope);
            scope.pop();
            scope.pop();
            ok
        }
        Term::FixGroup { bindings, .. } => {
            let start = scope.len();
            for binding in bindings {
                scope.push(binding.func.clone());
            }
            let ok = bindings.iter().all(|binding| {
                scope.push(binding.param.clone());
                let body_ok = closed_under(&binding.body, scope);
                scope.pop();
                body_ok
            });
            scope.truncate(start);
            ok
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            let scrut_ok = closed_under(scrutinee, scope);
            let zero_ok = closed_under(zero_body, scope);
            scope.push(succ_var.clone());
            let succ_ok = closed_under(succ_body, scope);
            scope.pop();
            scrut_ok && zero_ok && succ_ok
        }
        Term::Handle { body, handler } => {
            let body_ok = closed_under(body, scope);
            scope.push(handler.return_var.clone());
            let ret_ok = closed_under(&handler.return_body, scope);
            scope.pop();
            let clauses_ok = handler.clauses.iter().all(|clause| {
                scope.push(clause.op_param.clone());
                scope.push(clause.op_k.clone());
                let ok = closed_under(&clause.op_body, scope);
                scope.pop();
                scope.pop();
                ok
            });
            body_ok && ret_ok && clauses_ok
        }
        Term::Resume { kont, arg } => closed_under(kont, scope) && closed_under(arg, scope),
    }
}
