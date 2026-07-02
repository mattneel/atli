//! Graded checker for the reduced Atli core.
//!
//! The checker implements the executable Sprint 03 version of `docs/calculus.md §4` and
//! emits boundedness constraints for the `§7` solver. It deliberately does not call
//! `gen::derive_witness`; differential tests compare these independent implementations.
//!
//! Phase gate (`docs/calculus.md §7.3`, with §2.3's under-allocation warning):
//! `CheckedWitness` is constructible only from `CertifiedGrade`, never from
//! `PendingGrade`; `SolverCertificate` is sealed inside `check::solve`, so callers cannot
//! mint certification maps outside a completed `solve()` run.
//!
//! ```compile_fail
//! use atli::check::{CheckedWitness, PendingGrade};
//! use atli::check::solve::BoundExpr;
//! use atli::grade::Bound;
//! let pending: PendingGrade<()> = PendingGrade::new(BoundExpr::constant(Bound::ZERO));
//! let _ = CheckedWitness::from_pending_for_doctest(pending);
//! ```
//!
//! ```compile_fail
//! use atli::check::solve::SolverCertificate;
//! let _ = SolverCertificate { values: Default::default() };
//! ```

mod error;
pub mod solve;

use std::collections::BTreeSet;

pub use error::{TypeError, TypeErrorKind};
pub use solve::{CertifiedGrade, PendingGrade, SolverCertificate, SolverStats};

use crate::core::{
    ContinuationUseFacts, CoverageTag, Divergence, FixBinding, Handler, RecursionTag, Term, Type,
    Witness,
};
use crate::grade::{Bound, Eff, Region};
use solve::{solve, BoundExpr, ConstraintSystem, UnknownId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedWitness {
    witness: Witness,
    stats: SolverStats,
    certified_bound: CertifiedGrade,
}

impl CheckedWitness {
    #[must_use]
    pub fn witness(&self) -> &Witness {
        &self.witness
    }

    #[must_use]
    pub fn solver_stats(&self) -> &SolverStats {
        &self.stats
    }

    /// Certified allocation grade for downstream consumers (`docs/calculus.md §7.3`, §9.1).
    #[must_use]
    pub fn certified_bound(&self) -> CertifiedGrade {
        self.certified_bound
    }

    fn new(mut partial: PartialWitness, certified: CertifiedGrade, stats: SolverStats) -> Self {
        partial.bound = BoundExpr::constant(certified.get());
        let witness = partial.into_witness(certified.get());
        Self {
            witness,
            stats,
            certified_bound: certified,
        }
    }
}

pub fn check(term: &Term) -> Result<CheckedWitness, TypeError> {
    let mut checker = Checker {
        system: ConstraintSystem::new(),
    };
    let partial = checker.infer(term, &Env::default())?;
    let output = solve(&checker.system);
    let pending = PendingGrade::<CheckedWitness>::new(partial.bound.clone());
    let certified = pending.certify(&output.certificate);
    Ok(CheckedWitness::new(partial, certified, output.stats))
}

#[derive(Debug, Clone)]
struct PartialWitness {
    ty: Type,
    effects: Eff,
    bound: BoundExpr,
    region: Region,
    continuation_uses: ContinuationUseFacts,
    divergence: Divergence,
    coverage: BTreeSet<CoverageTag>,
}

impl PartialWitness {
    fn pure(ty: Type) -> Self {
        Self {
            ty,
            effects: Eff::empty(),
            bound: BoundExpr::constant(Bound::ZERO),
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

    fn combine(mut self, rhs: &Self) -> Self {
        self.effects = self.effects.join(&rhs.effects);
        self.bound = self.bound.seq(rhs.bound.clone());
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

    fn into_witness(self, bound: Bound) -> Witness {
        Witness {
            ty: self.ty,
            effects: self.effects,
            bound,
            region: self.region,
            continuation_uses: self.continuation_uses,
            divergence: self.divergence,
            coverage: self.coverage,
        }
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

    fn lookup(&self, name: &str) -> Option<Type> {
        self.vars
            .iter()
            .rev()
            .find(|(found, _)| found == name)
            .map(|(_, ty)| ty.clone())
    }
}

#[derive(Debug, Clone)]
struct RecContext {
    func: String,
    param: String,
    tag: RecursionTag,
    strict_var: Option<String>,
    unknown: UnknownId,
}

struct Checker {
    system: ConstraintSystem,
}

impl Checker {
    fn infer(&mut self, term: &Term, env: &Env) -> Result<PartialWitness, TypeError> {
        match term {
            Term::Unit => Ok(PartialWitness::pure(Type::Unit)),
            Term::Zero => Ok(PartialWitness::pure(Type::Nat)),
            Term::Array(_) => Ok(PartialWitness::pure(Type::Array)),
            Term::Succ(inner) => {
                let mut out = self.infer(inner, env)?;
                expect_type(&out.ty, &Type::Nat, term, "Succ", "§4.2")?;
                out.ty = Type::Nat;
                out.bound = contextualize(&out);
                Ok(out)
            }
            Term::Var(name) => env.lookup(name).map(PartialWitness::pure).ok_or_else(|| {
                TypeError::new(
                    "Var",
                    "§4.1",
                    term,
                    format!("unbound variable `{name}`"),
                    TypeErrorKind::UnboundVariable(name.clone()),
                )
            }),
            Term::MkArray(len, fill) => {
                let len_w = self.infer(len, env)?;
                expect_type(&len_w.ty, &Type::Nat, term, "MkArray", "§4.5.1")?;
                let fill_w = self.infer(fill, env)?;
                expect_type(&fill_w.ty, &Type::Nat, term, "MkArray", "§4.5.1")?;
                let mut out = len_w.combine(&fill_w);
                out.ty = Type::Array;
                out.coverage.insert(CoverageTag::Array);
                Ok(out)
            }
            Term::ArrayGet(array, index) => {
                let array_w = self.infer(array, env)?;
                expect_type(&array_w.ty, &Type::Array, term, "Array-Get", "§4.5.1")?;
                let index_w = self.infer(index, env)?;
                expect_type(&index_w.ty, &Type::Nat, term, "Array-Get", "§4.5.1")?;
                let mut out = array_w.combine(&index_w);
                out.ty = Type::Nat;
                out.coverage.insert(CoverageTag::Array);
                Ok(out)
            }
            Term::ArraySet(array, index, value) => {
                let array_w = self.infer(array, env)?;
                expect_type(&array_w.ty, &Type::Array, term, "Array-Set", "§4.5.1")?;
                let index_w = self.infer(index, env)?;
                expect_type(&index_w.ty, &Type::Nat, term, "Array-Set", "§4.5.1")?;
                let value_w = self.infer(value, env)?;
                expect_type(&value_w.ty, &Type::Nat, term, "Array-Set", "§4.5.1")?;
                let mut out = array_w.combine(&index_w).combine(&value_w);
                out.ty = Type::Array;
                out.coverage.insert(CoverageTag::Array);
                Ok(out)
            }
            Term::ArrayLen(array) => {
                let mut out = self.infer(array, env)?;
                expect_type(&out.ty, &Type::Array, term, "Array-Len", "§4.5.1")?;
                out.ty = Type::Nat;
                out.coverage.insert(CoverageTag::Array);
                Ok(out)
            }
            Term::Move(inner) | Term::Inplace(inner) | Term::Freeze(inner) => {
                let mut out = self.infer(inner, env)?;
                out.coverage.insert(CoverageTag::Array);
                Ok(out)
            }
            Term::Lam {
                param,
                param_ty,
                body,
            } => {
                let body = self.infer(body, &env.with_var(param.clone(), param_ty.clone()))?;
                Ok(PartialWitness::pure(Type::Arrow(
                    Box::new(param_ty.clone()),
                    Box::new(body.ty),
                )))
            }
            Term::App(fun, arg) => self.infer_app(fun, arg, env, term),
            Term::Let { var, expr, body } => {
                let expr_w = self.infer(expr, env)?;
                let body_w = self.infer(body, &env.with_var(var.clone(), expr_w.ty.clone()))?;
                let result_ty = body_w.ty.clone();
                let expr_bound = contextualize(&expr_w);
                let mut out = expr_w.combine(&body_w);
                out.ty = result_ty;
                out.bound = expr_bound.seq(body_w.bound);
                out.coverage.insert(CoverageTag::Let);
                Ok(out)
            }
            Term::CaseNat {
                scrutinee,
                zero_body,
                succ_var,
                succ_body,
            } => self.infer_case(scrutinee, zero_body, succ_var, succ_body, env, term),
            Term::Fix { .. } => self.infer_fix(term, env),
            Term::FixGroup { bindings, entry } => self.infer_fix_group(bindings, entry, env, term),
            Term::Perform(label, arg) => {
                let mut out = self.infer(arg, env)?;
                expect_type(&out.ty, &Type::Nat, term, "Perform", "§4.6")?;
                out.ty = Type::Nat;
                out.effects = out.effects.join(&Eff::singleton(*label));
                out.coverage.insert(CoverageTag::Perform);
                Ok(out)
            }
            Term::Handle { body, handler } => self.infer_handle(body, handler, env, term),
            Term::Resume { kont, arg } => {
                let arg_w = self.infer(arg, env)?;
                let kont_resumes =
                    matches!(&**kont, Term::Var(name) if env.cont_vars.contains(name));
                let kont_ty = if kont_resumes {
                    Type::Cont(Box::new(Type::Nat), Box::new(Type::Nat))
                } else {
                    self.infer(kont, env)?.ty
                };
                if !matches!(kont_ty, Type::Cont(_, _)) {
                    return Err(TypeError::new(
                        "Resume",
                        "§4.7/§5",
                        term,
                        format!("expected continuation, found {kont_ty}"),
                        TypeErrorKind::ExpectedContinuation(kont_ty),
                    ));
                }
                let mut out = arg_w;
                expect_type(&out.ty, &Type::Nat, term, "Resume", "§4.7/§5")?;
                out.ty = Type::Nat;
                if kont_resumes {
                    out.continuation_uses.resumed += 1;
                }
                Ok(out)
            }
            Term::Cont(_) => Ok(PartialWitness::pure(Type::Cont(
                Box::new(Type::Nat),
                Box::new(Type::Nat),
            ))),
        }
    }

    fn infer_app(
        &mut self,
        fun: &Term,
        arg: &Term,
        env: &Env,
        whole: &Term,
    ) -> Result<PartialWitness, TypeError> {
        if let Term::Var(func) = fun {
            if let Some(rec) = env.recs.iter().find(|rec| &rec.func == func) {
                let arg_w = self.infer(arg, env)?;
                expect_type(&arg_w.ty, &Type::Nat, whole, "App/Fix", "§4.8/§7.1")?;
                if env
                    .rec
                    .as_ref()
                    .is_some_and(|current| current.tag == RecursionTag::Structural)
                    && env
                        .rec
                        .as_ref()
                        .is_none_or(|current| current.func != rec.func)
                {
                    return Err(TypeError::new(
                        "FixGroup-Structural",
                        "§4.8/§7.1",
                        whole,
                        format!(
                            "Structural `{}` calls group member `{}` forming a cycle; cyclic groups require `measure` or `div`",
                            env.rec.as_ref().map_or("<unknown>", |current| current.func.as_str()),
                            rec.func
                        ),
                        TypeErrorKind::NonStrictStructuralRecursion,
                    ));
                }
                let strict = matches!(arg, Term::Var(name) if rec.strict_var.as_ref() == Some(name))
                    || matches!(
                        (arg, env.rec.as_ref()),
                        (Term::Var(name), Some(current)) if current.func == rec.func && name != &current.param
                    );
                let mut out = arg_w;
                out.ty = Type::Nat;
                out.bound = match rec.tag {
                    RecursionTag::Structural
                        if strict
                            && env
                                .rec
                                .as_ref()
                                .is_some_and(|current| current.func == rec.func) =>
                    {
                        BoundExpr::constant(Bound::finite(1))
                    }
                    RecursionTag::Structural => {
                        return Err(TypeError::new(
                            "Fix-Structural",
                            "§4.8/§7.1",
                            whole,
                            "recursive call argument is not the peeled predecessor",
                            TypeErrorKind::NonStrictStructuralRecursion,
                        ));
                    }
                    RecursionTag::Measure
                        if env
                            .rec
                            .as_ref()
                            .is_some_and(|current| current.func != rec.func) =>
                    {
                        // `fix*` constraints (`calculus.md §7.1`) expose sibling calls as
                        // dependencies so generated mutual groups exercise multi-node SCCs.
                        // Self `measure` calls keep Sprint 03's trusted finite rung.
                        BoundExpr::unknown(rec.unknown).join(BoundExpr::constant(Bound::finite(1)))
                    }
                    RecursionTag::Measure => BoundExpr::constant(Bound::finite(1)),
                    RecursionTag::Div => {
                        BoundExpr::unknown(rec.unknown).seq(BoundExpr::constant(Bound::finite(1)))
                    }
                };
                if rec.tag == RecursionTag::Div {
                    out.divergence = Divergence::Div;
                }
                return Ok(out);
            }
        }

        if let Term::Lam {
            param,
            param_ty,
            body,
        } = fun
        {
            let arg_w = self.infer(arg, env)?;
            expect_type(&arg_w.ty, param_ty, whole, "App", "§4.3")?;
            let body_w = self.infer(body, &env.with_var(param.clone(), param_ty.clone()))?;
            let result_ty = body_w.ty.clone();
            let arg_bound = contextualize(&arg_w);
            let mut out = arg_w.combine(&body_w);
            out.ty = result_ty;
            out.bound = arg_bound.seq(body_w.bound);
            out.coverage.insert(CoverageTag::LambdaApp);
            return Ok(out);
        }

        let fun_w = self.infer(fun, env)?;
        let arg_w = self.infer(arg, env)?;
        let result_ty = match &fun_w.ty {
            Type::Arrow(arg_ty, ret_ty) => {
                expect_type(&arg_w.ty, arg_ty, whole, "App", "§4.3")?;
                (**ret_ty).clone()
            }
            other => {
                return Err(TypeError::new(
                    "App",
                    "§4.3",
                    whole,
                    format!("expected function, found {other}"),
                    TypeErrorKind::ExpectedFunction(other.clone()),
                ));
            }
        };
        let fun_bound = contextualize(&fun_w);
        let arg_bound = contextualize(&arg_w);
        let mut out = fun_w.combine(&arg_w);
        out.ty = result_ty;
        out.bound = fun_bound.seq(arg_bound);
        Ok(out)
    }

    fn infer_case(
        &mut self,
        scrutinee: &Term,
        zero_body: &Term,
        succ_var: &str,
        succ_body: &Term,
        env: &Env,
        whole: &Term,
    ) -> Result<PartialWitness, TypeError> {
        let scrut_w = self.infer(scrutinee, env)?;
        expect_type(&scrut_w.ty, &Type::Nat, whole, "Case-Nat", "§4.2")?;
        let zero_w = self.infer(zero_body, env)?;
        let succ_env = env.with_var(succ_var.into(), Type::Nat);
        let succ_env = if matches!(scrutinee, Term::Var(name) if env.rec.as_ref().is_some_and(|rec| rec.param == *name))
        {
            succ_env.with_strict_var(succ_var)
        } else {
            succ_env
        };
        let succ_w = self.infer(succ_body, &succ_env)?;
        expect_type(&succ_w.ty, &zero_w.ty, whole, "Case-Nat", "§4.2")?;
        let scrut_bound = contextualize(&scrut_w);
        let result_ty = zero_w.ty.clone();
        let branch_bound = zero_w.bound.clone().join(succ_w.bound.clone());
        let divergence = case_divergence(scrutinee, &scrut_w, &zero_w, &succ_w);
        let mut out = scrut_w.combine(&zero_w).combine(&succ_w);
        out.ty = result_ty;
        out.bound = scrut_bound.seq(branch_bound);
        out.divergence = divergence;
        Ok(out)
    }

    fn infer_fix(&mut self, whole: &Term, env: &Env) -> Result<PartialWitness, TypeError> {
        let Term::Fix {
            func,
            param,
            param_ty,
            body,
            tag,
        } = whole
        else {
            unreachable!("infer_fix is only called for fix terms")
        };
        expect_type(param_ty, &Type::Nat, whole, "Fix", "§4.8")?;
        let unknown = self.system.fresh_unknown();
        let rec = RecContext {
            func: func.clone(),
            param: param.clone(),
            tag: *tag,
            strict_var: None,
            unknown,
        };
        let body_w = self.infer(body, &env.with_rec(rec))?;
        let body_expr = body_w.bound.clone();
        let constraint = if *tag == RecursionTag::Div {
            BoundExpr::unknown(unknown).seq(BoundExpr::constant(Bound::finite(1)))
        } else {
            body_expr.clone()
        };
        self.system.constrain(unknown, constraint);
        let mut out = PartialWitness::pure(Type::Arrow(Box::new(Type::Nat), Box::new(body_w.ty)));
        out.coverage = body_w.coverage;
        out.bound = match tag {
            RecursionTag::Structural => BoundExpr::unknown(unknown),
            RecursionTag::Measure => {
                BoundExpr::unknown(unknown).join(BoundExpr::constant(Bound::finite(1)))
            }
            RecursionTag::Div => BoundExpr::unknown(unknown),
        };
        out.divergence = match tag {
            RecursionTag::Div => Divergence::Div,
            RecursionTag::Structural | RecursionTag::Measure => body_w.divergence,
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
        Ok(out)
    }

    fn infer_fix_group(
        &mut self,
        bindings: &[FixBinding],
        entry: &str,
        env: &Env,
        whole: &Term,
    ) -> Result<PartialWitness, TypeError> {
        // Binding-group typing (`calculus.md §4.8`) emits one β unknown per member; cyclic
        // groups therefore feed the existing SCC solver exactly as `§7.1` specifies.
        if bindings.is_empty() || !bindings.iter().any(|binding| binding.func == entry) {
            return Err(TypeError::new(
                "FixGroup",
                "§4.8",
                whole,
                format!("fix* entry `{entry}` is not a member of the binding group"),
                TypeErrorKind::Solver("malformed fix* entry".into()),
            ));
        }
        let recs = bindings
            .iter()
            .map(|binding| {
                expect_type(&binding.param_ty, &Type::Nat, whole, "FixGroup", "§4.8")?;
                Ok(RecContext {
                    func: binding.func.clone(),
                    param: binding.param.clone(),
                    tag: binding.tag,
                    strict_var: None,
                    unknown: self.system.fresh_unknown(),
                })
            })
            .collect::<Result<Vec<_>, TypeError>>()?;
        let mut entry_ty = Type::Nat;
        let mut entry_bound = BoundExpr::constant(Bound::ZERO);
        let mut entry_divergence = Divergence::Terminates;
        let mut coverage = BTreeSet::new();
        for binding in bindings {
            let body_env = env.with_rec_group(recs.clone(), &binding.func, &binding.param);
            let body_w = self.infer(&binding.body, &body_env)?;
            let rec = recs
                .iter()
                .find(|rec| rec.func == binding.func)
                .expect("binding has rec context");
            let constraint = if binding.tag == RecursionTag::Div {
                BoundExpr::unknown(rec.unknown).seq(BoundExpr::constant(Bound::finite(1)))
            } else {
                body_w.bound.clone()
            };
            self.system.constrain(rec.unknown, constraint);
            coverage.extend(body_w.coverage.iter().copied());
            match binding.tag {
                RecursionTag::Structural => {
                    coverage.insert(CoverageTag::FixStructural);
                }
                RecursionTag::Measure => {
                    coverage.insert(CoverageTag::FixMeasure);
                }
                RecursionTag::Div => {}
            }
            if binding.func == entry {
                entry_ty = body_w.ty.clone();
                entry_bound = match binding.tag {
                    RecursionTag::Structural => BoundExpr::unknown(rec.unknown),
                    RecursionTag::Measure => {
                        BoundExpr::unknown(rec.unknown).join(BoundExpr::constant(Bound::finite(1)))
                    }
                    RecursionTag::Div => BoundExpr::unknown(rec.unknown),
                };
                entry_divergence = if binding.tag == RecursionTag::Div {
                    Divergence::Div
                } else {
                    body_w.divergence
                };
            }
        }
        let mut out = PartialWitness::pure(Type::Arrow(Box::new(Type::Nat), Box::new(entry_ty)));
        out.bound = entry_bound;
        out.divergence = entry_divergence;
        out.coverage = coverage;
        Ok(out)
    }

    fn infer_handle(
        &mut self,
        body: &Term,
        handler: &Handler,
        env: &Env,
        whole: &Term,
    ) -> Result<PartialWitness, TypeError> {
        let body_w = self.infer(body, env)?;
        let ret_w = self.infer(
            &handler.return_body,
            &env.with_var(handler.return_var.clone(), body_w.ty.clone()),
        )?;
        let mut handled_effects = body_w.effects.clone();
        let mut op_effects = Eff::empty();
        let mut op_bound = BoundExpr::constant(Bound::ZERO);
        let mut op_region = Region::Arena;
        let mut introduced = 0;
        let mut resumes = 0;
        let mut op_diverges = false;
        let mut op_coverage = BTreeSet::new();
        for clause in &handler.clauses {
            let op_env = env
                .with_var(clause.op_param.clone(), Type::Nat)
                .with_cont(&clause.op_k);
            let op_w = self.infer(&clause.op_body, &op_env)?;
            expect_type(&op_w.ty, &ret_w.ty, whole, "Handle", "§4.7")?;
            let usage =
                classify_handler_k_usage(&clause.op_body, &clause.op_k).map_err(|message| {
                    TypeError::new(
                        "Handle",
                        "§4.7",
                        &clause.op_body,
                        format!("label {}: {message}", clause.op_label),
                        TypeErrorKind::HandlerContinuationUsage(message),
                    )
                })?;
            introduced += u32::from(body_w.effects.contains(clause.op_label));
            resumes += u32::from(usage == KUsage::Resumed);
            let effective = if usage == KUsage::Resumed {
                op_w.bound.clone().seq(body_w.bound.clone())
            } else {
                op_w.bound.clone()
            };
            op_bound = op_bound.join(effective);
            op_region = op_region.meet(op_w.region);
            op_effects = op_effects.join(&op_w.effects);
            op_diverges |= op_w.divergence == Divergence::Div;
            op_coverage.extend(op_w.coverage.iter().copied());
            handled_effects = handled_effects.without(clause.op_label);
            op_coverage.insert(if usage == KUsage::Resumed {
                CoverageTag::HandleResuming
            } else {
                CoverageTag::HandleDropped
            });
        }
        let dropped = introduced.saturating_sub(resumes);
        let mut out = PartialWitness::pure(ret_w.ty.clone());
        out.effects = handled_effects.join(&ret_w.effects).join(&op_effects);
        out.bound = ret_w.bound.clone().join(op_bound);
        out.region = body_w.region.meet(ret_w.region).meet(op_region);
        out.continuation_uses = ContinuationUseFacts {
            introduced,
            resumed: resumes,
            dropped,
        };
        out.divergence = if body_w.divergence == Divergence::Div
            || ret_w.divergence == Divergence::Div
            || op_diverges
        {
            Divergence::Div
        } else {
            Divergence::Terminates
        };
        out.coverage = body_w.coverage;
        out.coverage.extend(ret_w.coverage.iter().copied());
        out.coverage.extend(op_coverage);
        Ok(out)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KUsage {
    Dropped,
    Resumed,
}

fn classify_handler_k_usage(term: &Term, k: &str) -> Result<KUsage, String> {
    let mentions = free_var_count(term, k);
    let direct_resumes = direct_resume_count(term, k);
    match (mentions, direct_resumes) {
        (0, 0) => Ok(KUsage::Dropped),
        (1, 1) => Ok(KUsage::Resumed),
        (0, _) => Err("resume count impossible without k mention".into()),
        (_, 0) => Err(format!(
            "extra-mention: `{k}` appears free but is never directly resumed"
        )),
        _ => Err(format!(
            "one-resume-required: `{k}` has {mentions} free mentions and {direct_resumes} direct resumes"
        )),
    }
}

fn contextualize(child: &PartialWitness) -> BoundExpr {
    if !child.effects.is_empty() {
        child
            .bound
            .clone()
            .seq(BoundExpr::constant(Bound::finite(1)))
    } else {
        child.bound.clone()
    }
}

fn case_divergence(
    scrutinee: &Term,
    scrut_w: &PartialWitness,
    zero_w: &PartialWitness,
    succ_w: &PartialWitness,
) -> Divergence {
    if scrut_w.divergence == Divergence::Div {
        return Divergence::Div;
    }
    match scrutinee {
        Term::Zero => zero_w.divergence,
        Term::Succ(_) => succ_w.divergence,
        _ if zero_w.divergence == Divergence::Div && succ_w.divergence == Divergence::Div => {
            Divergence::Div
        }
        _ => Divergence::Terminates,
    }
}

fn expect_type(
    found: &Type,
    expected: &Type,
    term: &Term,
    rule: &'static str,
    section: &'static str,
) -> Result<(), TypeError> {
    if found == expected
        || matches!(
            (found, expected),
            (Type::Nat, Type::Array) | (Type::Array, Type::Nat)
        )
    {
        Ok(())
    } else {
        Err(TypeError::new(
            rule,
            section,
            term,
            format!("expected {expected}, found {found}"),
            TypeErrorKind::TypeMismatch {
                expected: expected.clone(),
                found: found.clone(),
            },
        ))
    }
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
        | Term::Freeze(inner) => free_var_count(inner, name),
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
            usize::from(!bindings.iter().any(|binding| binding.func == name))
                * bindings
                    .iter()
                    .map(|binding| {
                        usize::from(binding.param != name) * free_var_count(&binding.body, name)
                    })
                    .sum::<usize>()
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
            let nested = if here == 0 {
                direct_resume_count(kont, name)
            } else {
                0
            };
            here + nested + direct_resume_count(arg, name)
        }
        Term::Var(_) | Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => 0,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner) => direct_resume_count(inner, name),
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
            usize::from(!bindings.iter().any(|binding| binding.func == name))
                * bindings
                    .iter()
                    .map(|binding| {
                        usize::from(binding.param != name)
                            * direct_resume_count(&binding.body, name)
                    })
                    .sum::<usize>()
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
