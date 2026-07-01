//! Well-typed-by-construction term generator for Sprint 01.
//!
//! The generator is deliberately small and witness-producing. It follows the typing rules
//! as generation rules (`docs/calculus.md §4`) for the reduced target (`§10`) rather than
//! depending on a type checker, which is out of scope for Sprint 01. Witness `β` is derived
//! compositionally from the generated term by this module, not hand-authored per case.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{
    ContinuationUseFacts, CoverageTag, Divergence, GeneratedTerm, Handler, RecursionTag, Term,
    Type, Witness,
};
use crate::grade::{Bound, Eff, Label, Region};

pub const FIXED_SEED: u64 = 0xA711_0001;
pub const SAMPLE_SIZE: usize = 128;
pub const STEP_BUDGET: usize = 64;

#[must_use]
pub fn generated_case(selector: u8) -> GeneratedTerm {
    match selector % 8 {
        0 => build("unit", Term::unit()),
        1 => build("lambda_app", lambda_app_term(u64::from(selector))),
        2 => build("let", let_term(u64::from(selector))),
        3 => build("handle_resuming", handle_resuming_term()),
        4 => build("handle_dropped", handle_dropped_term()),
        5 => build("structural_fix", structural_fix_term()),
        6 => build("measured_fix", measured_fix_term()),
        _ => build("div_fix", div_fix_term()),
    }
}

#[must_use]
pub fn fixed_seed_sample() -> Vec<GeneratedTerm> {
    // Deterministic LCG over selectors. The fixed seed is reported in the sprint report and
    // is intentionally independent of proptest internals for stable coverage accounting.
    let mut state = FIXED_SEED;
    let mut sample = (0_u8..8).map(generated_case).collect::<Vec<_>>();
    while sample.len() < SAMPLE_SIZE {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        sample.push(generated_case((state >> 32) as u8));
    }
    sample
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

fn build(name: &'static str, term: Term) -> GeneratedTerm {
    let witness = derive_witness(&term);
    GeneratedTerm {
        term,
        witness,
        name,
    }
}

fn lambda_app_term(value: u64) -> Term {
    Term::App(
        Box::new(Term::Lam {
            param: "x".into(),
            param_ty: Type::Nat,
            body: Box::new(Term::var("x")),
        }),
        Box::new(Term::nat(value % 4)),
    )
}

fn let_term(value: u64) -> Term {
    Term::Let {
        var: "x".into(),
        expr: Box::new(Term::nat(value % 5)),
        body: Box::new(Term::var("x")),
    }
}

fn handle_resuming_term() -> Term {
    let body = Term::Let {
        var: "a".into(),
        expr: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        body: Box::new(Term::var("a")),
    };
    let op_body = Term::Resume {
        kont: Box::new(Term::var("k")),
        arg: Box::new(Term::var("p")),
    };
    Term::Handle {
        body: Box::new(body),
        handler: identity_handler(op_body),
    }
}

fn handle_dropped_term() -> Term {
    Term::Handle {
        body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        handler: identity_handler(Term::nat(3)),
    }
}

fn structural_fix_term() -> Term {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::CaseNat {
            scrutinee: Box::new(Term::var("x")),
            zero_body: Box::new(Term::zero()),
            succ_var: "pred".into(),
            succ_body: Box::new(Term::App(
                Box::new(Term::var("f")),
                Box::new(Term::var("pred")),
            )),
        }),
        tag: RecursionTag::Structural,
    };
    Term::App(Box::new(fix), Box::new(Term::nat(3)))
}

fn measured_fix_term() -> Term {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::CaseNat {
            scrutinee: Box::new(Term::var("x")),
            zero_body: Box::new(Term::zero()),
            succ_var: "_pred".into(),
            // Non-structural: the recursive argument is not the peeled predecessor. The
            // `Measure` tag is the generator's witness that this is accepted by the
            // annotated rung instead of the structural/free rung.
            succ_body: Box::new(Term::App(Box::new(Term::var("f")), Box::new(Term::zero()))),
        }),
        tag: RecursionTag::Measure,
    };
    Term::App(Box::new(fix), Box::new(Term::nat(3)))
}

fn div_fix_term() -> Term {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::App(
            Box::new(Term::var("f")),
            Box::new(Term::var("x")),
        )),
        tag: RecursionTag::Div,
    };
    Term::App(Box::new(fix), Box::new(Term::zero()))
}

fn identity_handler(op_body: Term) -> Handler {
    Handler {
        return_var: "r".into(),
        return_body: Box::new(Term::var("r")),
        op_label: Label::L,
        op_param: "p".into(),
        op_k: "k".into(),
        op_body: Box::new(op_body),
    }
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: BTreeMap<String, Type>,
    cont_vars: BTreeSet<String>,
    rec: Option<RecContext>,
}

impl Env {
    fn with_var(&self, name: &str, ty: Type) -> Self {
        let mut next = self.clone();
        next.vars.insert(name.into(), ty);
        next
    }

    fn with_cont(&self, name: &str) -> Self {
        let mut next = self.with_var(name, Type::Cont(Box::new(Type::Nat), Box::new(Type::Nat)));
        next.cont_vars.insert(name.into());
        next
    }

    fn with_rec(&self, rec: RecContext) -> Self {
        let mut next = self.clone();
        next.vars.insert(
            rec.func.clone(),
            Type::Arrow(Box::new(Type::Nat), Box::new(Type::Nat)),
        );
        next.vars.insert(rec.param.clone(), Type::Nat);
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

fn derive(term: &Term, env: &Env) -> Derived {
    match term {
        Term::Unit => Derived::pure(Type::Unit),
        Term::Zero => Derived::pure(Type::Nat),
        Term::Succ(inner) => {
            let inner = derive(inner, env);
            debug_assert_eq!(inner.ty, Type::Nat);
            Derived {
                ty: Type::Nat,
                ..inner
            }
        }
        Term::Var(name) => Derived::pure(env.vars.get(name).cloned().unwrap_or(Type::Nat)),
        Term::Lam {
            param,
            param_ty,
            body,
        } => {
            let body = derive(body, &env.with_var(param, param_ty.clone()));
            Derived::pure(Type::Arrow(Box::new(param_ty.clone()), Box::new(body.ty)))
        }
        Term::App(fun, arg) => derive_app(fun, arg, env),
        Term::Let { var, expr, body } => {
            let expr_d = derive(expr, env);
            let body_d = derive(body, &env.with_var(var, expr_d.ty.clone()));
            let mut out = expr_d.combine(&body_d);
            out.ty = body_d.ty;
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
            let succ_env = env.with_var(succ_var, Type::Nat);
            let succ_env = if matches!(&**scrutinee, Term::Var(name) if env.rec.as_ref().is_some_and(|rec| rec.param == *name))
            {
                succ_env.with_strict_var(succ_var)
            } else {
                succ_env
            };
            let succ_d = derive(succ_body, &succ_env);
            debug_assert_eq!(scrut_d.ty, Type::Nat);
            debug_assert_eq!(zero_d.ty, succ_d.ty);
            let scrut_bound = scrut_d.bound;
            let result_ty = zero_d.ty.clone();
            let branch_bound = zero_d.bound.join(succ_d.bound);
            let mut out = scrut_d.combine(&zero_d).combine(&succ_d);
            out.ty = result_ty;
            out.bound = scrut_bound.sequential(branch_bound);
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
            out.bound = out.bound.sequential(Bound::finite(1));
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

    let fun_d = derive(fun, env);
    let arg_d = derive(arg, env);
    let result_ty = match &fun_d.ty {
        Type::Arrow(_, ret) => (**ret).clone(),
        _ => Type::Nat,
    };
    let mut out = fun_d.combine(&arg_d);
    out.ty = result_ty;
    if matches!(fun, Term::Lam { .. }) {
        out.coverage.insert(CoverageTag::LambdaApp);
    }
    out
}

fn derive_handle(body: &Term, handler: &Handler, env: &Env) -> Derived {
    let body_d = derive(body, env);
    let ret_d = derive(
        &handler.return_body,
        &env.with_var(&handler.return_var, body_d.ty.clone()),
    );
    let op_env = env
        .with_var(&handler.op_param, Type::Nat)
        .with_cont(&handler.op_k);
    let op_d = derive(&handler.op_body, &op_env);
    let introduced = u32::from(body_d.effects.contains(handler.op_label));
    let resumes = op_d.continuation_uses.resumed;
    let dropped = introduced.saturating_sub(resumes);
    let op_effective_bound = if resumes > 0 {
        op_d.bound.sequential(body_d.bound)
    } else {
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
