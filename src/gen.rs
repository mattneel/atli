//! Type-directed compositional term generation for Sprint 02.
//!
//! Generation follows the reduced typing rules in `docs/calculus.md §4`: the builder is
//! given a target type, a typing environment, and a depth budget, then recursively chooses
//! introduction/elimination forms for that target. The invariant is that every generated
//! **safe** term is closed, well-typed at its target type, and uses each continuation
//! variable at most once; explicitly tagged negative terms are limited to top-level
//! `perform ℓ` detection fixtures. Shrinking is by choice bytes: a shrunk choice sequence
//! regenerates the term and then re-runs `derive_witness`, so witness metadata is never
//! stale.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{
    ContinuationUseFacts, CoverageTag, Divergence, ExpectedOutcome, GeneratedTerm, GenerationFacts,
    Handler, RecursionTag, Term, Type, Witness,
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
    let mut builder = Builder::new(ChoiceStream::new(choices));
    let top_choice = builder.choices.next_mod(12);
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
            choices.push((case % 12) as u8);
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
        Handler {
            return_var: "r".into(),
            return_body: Box::new(Term::var("r")),
            op_label: Label::L,
            op_param: "p".into(),
            op_k: "k".into(),
            op_body: Box::new(op_body),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: Vec<(String, Type)>,
    cont_vars: BTreeSet<String>,
    rec: Option<RecContext>,
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
        next.rec = Some(rec);
        next
    }

    fn with_strict_var(&self, strict_var: &str) -> Self {
        let mut next = self.clone();
        if let Some(rec) = &mut next.rec {
            rec.strict_var = Some(strict_var.into());
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
    if effectful_child.effects.contains(Label::L) {
        effectful_child.bound.sequential(Bound::finite(1))
    } else {
        effectful_child.bound
    }
}

fn derive(term: &Term, env: &Env) -> Derived {
    match term {
        Term::Unit => Derived::pure(Type::Unit),
        Term::Zero => Derived::pure(Type::Nat),
        Term::Succ(inner) => {
            let inner = derive(inner, env);
            debug_assert_eq!(inner.ty, Type::Nat);
            let mut out = inner;
            out.ty = Type::Nat;
            out.bound = contextualize(&out);
            out
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
            debug_assert_eq!(*param_ty, Type::Nat);
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
    if let (Term::Var(func), Some(rec)) = (fun, env.rec.as_ref()) {
        if func == &rec.func {
            let arg_d = derive(arg, env);
            let strict = matches!(arg, Term::Var(name) if rec.strict_var.as_ref() == Some(name));
            let mut out = arg_d;
            out.ty = Type::Nat;
            out.bound = match rec.tag {
                RecursionTag::Structural if strict => Bound::finite(1),
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

fn derive_handle(body: &Term, handler: &Handler, env: &Env) -> Derived {
    let body_d = derive(body, env);
    let ret_d = derive(
        &handler.return_body,
        &env.with_var(handler.return_var.clone(), body_d.ty.clone()),
    );
    let op_env = env
        .with_var(handler.op_param.clone(), Type::Nat)
        .with_cont(&handler.op_k);
    let op_d = derive(&handler.op_body, &op_env);
    let introduced = u32::from(body_d.effects.contains(handler.op_label));
    let resumes = op_d.continuation_uses.resumed;
    let dropped = introduced.saturating_sub(resumes);
    let op_effective_bound = if resumes > 0 {
        // Lazy `H-op-resume` (`calculus.md §5`) materializes the deep one-shot
        // continuation, so the `Handle` rule (`§4.7`) adds the carried body `β`.
        op_d.bound.sequential(body_d.bound)
    } else {
        // Lazy `H-op-drop` does not materialize `k`; dropped exception/default clauses
        // keep `β̂ᵢ = βᵢ` (`calculus.md §4.7`).
        op_d.bound
    };
    let mut out = Derived::pure(ret_d.ty.clone());
    out.effects = body_d
        .effects
        .without(handler.op_label)
        .join(&ret_d.effects)
        .join(&op_d.effects);
    out.bound = ret_d.bound.join(op_effective_bound);
    out.region = body_d.region.meet(ret_d.region).meet(op_d.region);
    out.continuation_uses = ContinuationUseFacts {
        introduced,
        resumed: resumes,
        dropped,
    };
    out.divergence = if body_d.divergence == Divergence::Div
        || ret_d.divergence == Divergence::Div
        || op_d.divergence == Divergence::Div
    {
        Divergence::Div
    } else {
        Divergence::Terminates
    };
    out.coverage = body_d.coverage;
    out.coverage.extend(ret_d.coverage.iter().copied());
    out.coverage.extend(op_d.coverage.iter().copied());
    out.coverage.insert(if resumes > 0 {
        CoverageTag::HandleResuming
    } else {
        CoverageTag::HandleDropped
    });
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
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) => 1,
        Term::Succ(inner) | Term::Perform(_, inner) => 1 + term_depth(inner),
        Term::Lam { body, .. } | Term::Fix { body, .. } => 1 + term_depth(body),
        Term::App(fun, arg) => 1 + term_depth(fun).max(term_depth(arg)),
        Term::Let { expr, body, .. } => 1 + term_depth(expr).max(term_depth(body)),
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_body,
            ..
        } => 1 + term_depth(scrutinee).max(term_depth(zero_body).max(term_depth(succ_body))),
        Term::Handle { body, handler } => 1 + term_depth(body).max(term_depth(&handler.op_body)),
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
            scan_handlers(&handler.op_body, true, facts);
        }
        Term::Succ(inner) | Term::Perform(_, inner) => scan_handlers(inner, in_handler, facts),
        Term::Lam { body, .. } | Term::Fix { body, .. } => scan_handlers(body, in_handler, facts),
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
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) => {}
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
        Term::App(fun, arg) => {
            if let Term::Var(func) = &**fun {
                if let Some(rec) = stack.iter().rev().find(|rec| rec.func == *func) {
                    let strict =
                        matches!(&**arg, Term::Var(arg_name) if rec.strict_vars.contains(arg_name));
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
        Term::Succ(inner) | Term::Perform(_, inner) => scan_rec_calls(inner, stack, facts),
        Term::Lam { body, .. } => scan_rec_calls(body, stack, facts),
        Term::Let { expr, body, .. } => {
            scan_rec_calls(expr, stack, facts);
            scan_rec_calls(body, stack, facts);
        }
        Term::Handle { body, handler } => {
            scan_rec_calls(body, stack, facts);
            scan_rec_calls(&handler.return_body, stack, facts);
            scan_rec_calls(&handler.op_body, stack, facts);
        }
        Term::Resume { kont, arg } => {
            scan_rec_calls(kont, stack, facts);
            scan_rec_calls(arg, stack, facts);
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) => {}
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
                && term_obeys_continuation_usage_under(&handler.op_body)
                && handler_clause_obeys_k_usage(&handler.op_body, &handler.op_k)
        }
        Term::Succ(inner) | Term::Perform(_, inner) => term_obeys_continuation_usage_under(inner),
        Term::Lam { body, .. } | Term::Fix { body, .. } => {
            term_obeys_continuation_usage_under(body)
        }
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
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) => true,
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
        Term::Unit | Term::Zero | Term::Cont(_) => 0,
        Term::Succ(inner) | Term::Perform(_, inner) => free_var_count(inner, name),
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
                + usize::from(handler.op_param != name && handler.op_k != name)
                    * free_var_count(&handler.op_body, name)
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
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) => 0,
        Term::Succ(inner) | Term::Perform(_, inner) => direct_resume_count(inner, name),
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
                + usize::from(handler.op_param != name && handler.op_k != name)
                    * direct_resume_count(&handler.op_body, name)
        }
    }
}

fn closed_under(term: &Term, scope: &mut Vec<String>) -> bool {
    match term {
        Term::Var(name) => scope.contains(name),
        Term::Unit | Term::Zero | Term::Cont(_) => true,
        Term::Succ(inner) | Term::Perform(_, inner) => closed_under(inner, scope),
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
            scope.push(handler.op_param.clone());
            scope.push(handler.op_k.clone());
            let op_ok = closed_under(&handler.op_body, scope);
            scope.pop();
            scope.pop();
            body_ok && ret_ok && op_ok
        }
        Term::Resume { kont, arg } => closed_under(kont, scope) && closed_under(arg, scope),
    }
}
