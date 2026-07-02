//! Small-step reference interpreter for the reduced core.
//!
//! Rule comments cite `docs/calculus.md §5`. The implementation is intentionally direct
//! and instrumented rather than optimized; it is the operational oracle for Sprint 01.

use std::collections::BTreeMap;

use crate::core::{ContId, Handler, RecursionTag, Term};
use crate::grade::Label;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    Beta,
    Let,
    CaseZero,
    CaseSucc,
    Unfold,
    HReturn,
    HOp,
    Resume,
    ArrayNew,
    ArrayGet,
    ArraySet,
    ArrayLen,
    Move,
    Freeze,
    Mark,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Value,
    Stepable,
    StuckDoubleResume,
    StuckUnhandledOperation,
    BudgetExhaustedDiv,
    BoundsTrap,
    InternalMalformed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalReport {
    pub outcome: Outcome,
    pub final_term: Term,
    pub trace: Vec<Rule>,
    pub max_frame: u32,
    pub data_allocs: u64,
}

impl EvalReport {
    #[must_use]
    pub fn normalized_for_determinism(&self) -> Self {
        Self {
            outcome: self.outcome.clone(),
            final_term: self.final_term.normalize_cont_ids(),
            trace: self.trace.clone(),
            max_frame: self.max_frame,
            data_allocs: self.data_allocs,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Continuation {
    used: bool,
    frames: Vec<Frame>,
    handler: Handler,
    frame_size: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Frame {
    AppFun(Box<Term>),
    AppArg(Box<Term>),
    Let {
        var: String,
        body: Box<Term>,
    },
    Perform(Label),
    ResumeKont(Box<Term>),
    ResumeArg(Box<Term>),
    Succ,
    CaseNat {
        zero_body: Box<Term>,
        succ_var: String,
        succ_body: Box<Term>,
    },
    Handle(Handler),
    MkArrayLen(Box<Term>),
    MkArrayFill(Box<Term>),
    ArrayGetArray(Box<Term>),
    ArrayGetIndex(Box<Term>),
    ArraySetArray(Box<Term>, Box<Term>),
    ArraySetIndex(Box<Term>, Box<Term>),
    ArraySetValue(Box<Term>, Box<Term>),
    ArrayLen,
    Move,
    Inplace,
    Freeze,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine {
    next_cont: u64,
    continuations: BTreeMap<u64, Continuation>,
    max_frame: u32,
    data_allocs: u64,
}

impl Default for Machine {
    fn default() -> Self {
        Self::new()
    }
}

impl Machine {
    #[must_use]
    pub fn new() -> Self {
        Self {
            next_cont: 0,
            continuations: BTreeMap::new(),
            max_frame: 0,
            data_allocs: 0,
        }
    }

    #[must_use]
    pub fn max_frame(&self) -> u32 {
        self.max_frame
    }

    pub fn eval(&mut self, term: Term, budget: usize, expect_div: bool) -> EvalReport {
        let mut current = term;
        let mut trace = Vec::new();
        for _ in 0..budget {
            if current.is_value() {
                return EvalReport {
                    outcome: Outcome::Value,
                    final_term: current,
                    trace,
                    max_frame: self.max_frame,
                    data_allocs: self.data_allocs,
                };
            }
            match self.step(current) {
                StepResult::Stepped { term, rule } => {
                    current = term;
                    trace.push(rule);
                }
                StepResult::Stuck(outcome, term) => {
                    return EvalReport {
                        outcome,
                        final_term: term,
                        trace,
                        max_frame: self.max_frame,
                        data_allocs: self.data_allocs,
                    };
                }
            }
        }
        EvalReport {
            outcome: if expect_div {
                Outcome::BudgetExhaustedDiv
            } else {
                Outcome::InternalMalformed
            },
            final_term: current,
            trace,
            max_frame: self.max_frame,
            data_allocs: self.data_allocs,
        }
    }

    pub fn step(&mut self, term: Term) -> StepResult {
        match term {
            // `((λx. e) v) → e[x := v]` (β), `calculus.md §5`.
            Term::App(fun, arg) => self.step_app(*fun, *arg),
            // `let x = v in e → e[x := v]` (let), `calculus.md §5`.
            Term::Let { var, expr, body } => self.step_let(var, *expr, *body),
            Term::Succ(inner) => self.step_succ(*inner),
            Term::MkArray(len, fill) => self.step_mkarray(*len, *fill),
            Term::ArrayGet(array, index) => self.step_array_get(*array, *index),
            Term::ArraySet(array, index, value) => self.step_array_set(*array, *index, *value),
            Term::ArrayLen(array) => self.step_array_len(*array),
            Term::Move(inner) => self.step_move(*inner),
            Term::Inplace(inner) => self.step_inplace(*inner),
            Term::Freeze(inner) => self.step_freeze(*inner),
            Term::Mark(_, inner) => StepResult::Stepped {
                term: *inner,
                rule: Rule::Mark,
            },
            Term::CaseNat {
                scrutinee,
                zero_body,
                succ_var,
                succ_body,
            } => self.step_case_nat(*scrutinee, *zero_body, succ_var, *succ_body),
            // `fix f. λx. e → λx. e[f := fix f. λx. e]` (unfold), `calculus.md §5`.
            Term::Fix {
                func,
                param,
                param_ty,
                body,
                tag,
            } => {
                let fix = Term::Fix {
                    func: func.clone(),
                    param: param.clone(),
                    param_ty: param_ty.clone(),
                    body: body.clone(),
                    tag,
                };
                let unfolded_body = body.subst(&func, &fix);
                StepResult::Stepped {
                    term: Term::Lam {
                        param,
                        param_ty,
                        body: Box::new(unfolded_body),
                    },
                    rule: Rule::Unfold,
                }
            }
            Term::FixGroup { bindings, entry } => self.step_fix_group(bindings, entry),
            Term::Perform(label, arg) => self.step_perform(label, *arg),
            Term::Handle { body, handler } => self.step_handle(*body, handler),
            // `resume κ v → κ v` if unused; otherwise stuck (`calculus.md §5`).
            Term::Resume { kont, arg } => self.step_resume(*kont, *arg),
            value_or_var => StepResult::Stuck(Outcome::InternalMalformed, value_or_var),
        }
    }

    fn step_fix_group(
        &mut self,
        bindings: Vec<crate::core::FixBinding>,
        entry: String,
    ) -> StepResult {
        // `fix*` group unfold (`calculus.md §5`, Sprint 09): selecting an entry exposes
        // that member's lambda body with every group name rebound to a projection of the
        // same binding group.
        let Some(binding) = bindings
            .iter()
            .find(|binding| binding.func == entry)
            .cloned()
        else {
            return StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::FixGroup { bindings, entry },
            );
        };
        let mut unfolded_body = (*binding.body).clone();
        for member in &bindings {
            let projection = Term::FixGroup {
                bindings: bindings.clone(),
                entry: member.func.clone(),
            };
            unfolded_body = unfolded_body.subst(&member.func, &projection);
        }
        StepResult::Stepped {
            term: Term::Lam {
                param: binding.param,
                param_ty: binding.param_ty,
                body: Box::new(unfolded_body),
            },
            rule: Rule::Unfold,
        }
    }

    fn step_succ(&mut self, inner: Term) -> StepResult {
        if inner.is_value() {
            StepResult::Stuck(Outcome::InternalMalformed, Term::Succ(Box::new(inner)))
        } else {
            self.step_nested(inner, |term| Term::Succ(Box::new(term)))
        }
    }

    fn step_case_nat(
        &mut self,
        scrutinee: Term,
        zero_body: Term,
        succ_var: String,
        succ_body: Term,
    ) -> StepResult {
        if !scrutinee.is_value() {
            return self.step_nested(scrutinee, |term| Term::CaseNat {
                scrutinee: Box::new(term),
                zero_body: Box::new(zero_body),
                succ_var,
                succ_body: Box::new(succ_body),
            });
        }
        match scrutinee {
            // `case zero { zero => e0; succ x => e1 } → e0` (case-zero),
            // `calculus.md §5`.
            Term::Zero => StepResult::Stepped {
                term: zero_body,
                rule: Rule::CaseZero,
            },
            // `case (succ v) { ...; succ x => e1 } → e1[x := v]` (case-succ),
            // `calculus.md §5`.
            Term::Succ(value) if value.is_value() => StepResult::Stepped {
                term: succ_body.subst(&succ_var, &value),
                rule: Rule::CaseSucc,
            },
            other => StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::CaseNat {
                    scrutinee: Box::new(other),
                    zero_body: Box::new(zero_body),
                    succ_var,
                    succ_body: Box::new(succ_body),
                },
            ),
        }
    }

    fn step_mkarray(&mut self, len: Term, fill: Term) -> StepResult {
        if !len.is_value() {
            return self.step_nested(len, |term| Term::MkArray(Box::new(term), Box::new(fill)));
        }
        if !fill.is_value() {
            return self.step_nested(fill, |term| Term::MkArray(Box::new(len), Box::new(term)));
        }
        let Some(len) = nat_to_u64(&len) else {
            return StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::MkArray(Box::new(len), Box::new(fill)),
            );
        };
        self.data_allocs += 1;
        StepResult::Stepped {
            term: Term::Array(vec![
                fill;
                usize::try_from(len).expect("Nat literal fits usize")
            ]),
            rule: Rule::ArrayNew,
        }
    }

    fn step_array_get(&mut self, array: Term, index: Term) -> StepResult {
        if !array.is_value() {
            return self.step_nested(array, |term| {
                Term::ArrayGet(Box::new(term), Box::new(index))
            });
        }
        if !index.is_value() {
            return self.step_nested(index, |term| {
                Term::ArrayGet(Box::new(array), Box::new(term))
            });
        }
        let (Term::Array(values), Some(index)) = (&array, nat_to_u64(&index)) else {
            return StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::ArrayGet(Box::new(array), Box::new(index)),
            );
        };
        let Some(value) = values.get(usize::try_from(index).expect("index fits usize")) else {
            return StepResult::Stuck(
                Outcome::BoundsTrap,
                Term::ArrayGet(Box::new(array), Box::new(u64_to_nat(index))),
            );
        };
        StepResult::Stepped {
            term: value.clone(),
            rule: Rule::ArrayGet,
        }
    }

    fn step_array_set(&mut self, array: Term, index: Term, value: Term) -> StepResult {
        if !array.is_value() {
            return self.step_nested(array, |term| {
                Term::ArraySet(Box::new(term), Box::new(index), Box::new(value))
            });
        }
        if !index.is_value() {
            return self.step_nested(index, |term| {
                Term::ArraySet(Box::new(array), Box::new(term), Box::new(value))
            });
        }
        if !value.is_value() {
            return self.step_nested(value, |term| {
                Term::ArraySet(Box::new(array), Box::new(index), Box::new(term))
            });
        }
        let (Term::Array(values), Some(index)) = (&array, nat_to_u64(&index)) else {
            return StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::ArraySet(Box::new(array), Box::new(index), Box::new(value)),
            );
        };
        let idx = usize::try_from(index).expect("index fits usize");
        if idx >= values.len() {
            return StepResult::Stuck(
                Outcome::BoundsTrap,
                Term::ArraySet(
                    Box::new(array),
                    Box::new(u64_to_nat(index)),
                    Box::new(value),
                ),
            );
        }
        let mut next = values.clone();
        next[idx] = value;
        self.data_allocs += 1;
        StepResult::Stepped {
            term: Term::Array(next),
            rule: Rule::ArraySet,
        }
    }

    fn step_array_len(&mut self, array: Term) -> StepResult {
        if !array.is_value() {
            return self.step_nested(array, |term| Term::ArrayLen(Box::new(term)));
        }
        let Term::Array(values) = array else {
            return StepResult::Stuck(Outcome::InternalMalformed, Term::ArrayLen(Box::new(array)));
        };
        StepResult::Stepped {
            term: u64_to_nat(u64::try_from(values.len()).expect("array length fits u64")),
            rule: Rule::ArrayLen,
        }
    }

    fn step_move(&mut self, inner: Term) -> StepResult {
        if inner.is_value() {
            StepResult::Stepped {
                term: inner,
                rule: Rule::Move,
            }
        } else {
            self.step_nested(inner, |term| Term::Move(Box::new(term)))
        }
    }

    fn step_freeze(&mut self, inner: Term) -> StepResult {
        if inner.is_value() {
            StepResult::Stepped {
                term: inner,
                rule: Rule::Freeze,
            }
        } else {
            self.step_nested(inner, |term| Term::Freeze(Box::new(term)))
        }
    }

    fn step_inplace(&mut self, inner: Term) -> StepResult {
        // Oracle semantics for `calculus.md §5` array-inplace remains always-copy:
        // compiled code cashes q=1 with mutation, while the reference interpreter
        // preserves the functional `set` result for differential value comparison.
        if let Term::ArraySet(array, index, value) = inner {
            self.step_array_set(*array, *index, *value)
        } else if inner.is_value() {
            StepResult::Stepped {
                term: inner,
                rule: Rule::Move,
            }
        } else {
            self.step_nested(inner, |term| Term::Inplace(Box::new(term)))
        }
    }

    fn step_app(&mut self, fun: Term, arg: Term) -> StepResult {
        if !fun.is_value() {
            return self.step_nested(fun, |term| Term::App(Box::new(term), Box::new(arg)));
        }
        if !arg.is_value() {
            return self.step_nested(arg, |term| Term::App(Box::new(fun), Box::new(term)));
        }
        match fun {
            Term::Lam { param, body, .. } => StepResult::Stepped {
                term: body.subst(&param, &arg),
                rule: Rule::Beta,
            },
            other => StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::App(Box::new(other), Box::new(arg)),
            ),
        }
    }

    fn step_let(&mut self, var: String, expr: Term, body: Term) -> StepResult {
        if expr.is_value() {
            StepResult::Stepped {
                term: body.subst(&var, &expr),
                rule: Rule::Let,
            }
        } else {
            self.step_nested(expr, |term| Term::Let {
                var,
                expr: Box::new(term),
                body: Box::new(body),
            })
        }
    }

    fn step_perform(&mut self, label: Label, arg: Term) -> StepResult {
        if arg.is_value() {
            StepResult::Stuck(
                Outcome::StuckUnhandledOperation,
                Term::Perform(label, Box::new(arg)),
            )
        } else {
            self.step_nested(arg, |term| Term::Perform(label, Box::new(term)))
        }
    }

    fn step_handle(&mut self, body: Term, handler: Handler) -> StepResult {
        if body.is_value() {
            // `handle v with H → e_r[x := v]` (H-return), `calculus.md §5`.
            return StepResult::Stepped {
                term: handler.return_body.subst(&handler.return_var, &body),
                rule: Rule::HReturn,
            };
        }

        if let Some(captured) = decompose_perform(&body) {
            if let Some(clause) = handler.clause_for(captured.label) {
                // Multi-label `H-op` (`calculus.md §5`, Sprint 08): dispatch to the
                // clause whose label matches the captured operation.
                let with_param = clause.op_body.subst(&clause.op_param, &captured.arg);
                if !term_mentions_var(&clause.op_body, &clause.op_k) {
                    // Lazy `H-op-drop` (`calculus.md §5`): a clause that does not use `k`
                    // receives the operation parameter without materializing the delimited
                    // continuation, so dropped/default handlers allocate no captured frame.
                    return StepResult::Stepped {
                        term: with_param,
                        rule: Rule::HOp,
                    };
                }

                let frame_size =
                    u32::try_from(captured.frames.len()).expect("frame depth fits u32");
                self.max_frame = self.max_frame.max(frame_size);
                let id = self.alloc_continuation(captured.frames, handler.clone(), frame_size);
                let with_k = with_param.subst(&clause.op_k, &Term::Cont(id));
                // Lazy `H-op-resume` (`calculus.md §5`): only clauses that use `k`
                // materialize deep `κ = λy. handle E[y] with H`, marked ONE-SHOT.
                return StepResult::Stepped {
                    term: with_k,
                    rule: Rule::HOp,
                };
            }
        }

        self.step_nested(body, |term| Term::Handle {
            body: Box::new(term),
            handler,
        })
    }

    fn step_resume(&mut self, kont: Term, arg: Term) -> StepResult {
        if !kont.is_value() {
            return self.step_nested(kont, |term| Term::Resume {
                kont: Box::new(term),
                arg: Box::new(arg),
            });
        }
        if !arg.is_value() {
            return self.step_nested(arg, |term| Term::Resume {
                kont: Box::new(kont),
                arg: Box::new(term),
            });
        }
        match kont {
            Term::Cont(id) => self.resume_continuation(id, arg),
            other => StepResult::Stuck(
                Outcome::InternalMalformed,
                Term::Resume {
                    kont: Box::new(other),
                    arg: Box::new(arg),
                },
            ),
        }
    }

    fn step_nested(&mut self, nested: Term, rebuild: impl FnOnce(Term) -> Term) -> StepResult {
        match self.step(nested) {
            StepResult::Stepped { term, rule } => StepResult::Stepped {
                term: rebuild(term),
                rule,
            },
            StepResult::Stuck(outcome, term) => StepResult::Stuck(outcome, rebuild(term)),
        }
    }

    fn alloc_continuation(
        &mut self,
        frames: Vec<Frame>,
        handler: Handler,
        frame_size: u32,
    ) -> ContId {
        let id = ContId(self.next_cont);
        self.next_cont = self
            .next_cont
            .checked_add(1)
            .expect("continuation id overflow");
        let previous = self.continuations.insert(
            id.0,
            Continuation {
                used: false,
                frames,
                handler,
                frame_size,
            },
        );
        assert!(previous.is_none(), "fresh continuation id must not collide");
        id
    }

    fn resume_continuation(&mut self, id: ContId, arg: Term) -> StepResult {
        let Some(cont) = self.continuations.get_mut(&id.0) else {
            return StepResult::Stuck(Outcome::InternalMalformed, Term::Cont(id));
        };
        if cont.used {
            return StepResult::Stuck(
                Outcome::StuckDoubleResume,
                Term::Resume {
                    kont: Box::new(Term::Cont(id)),
                    arg: Box::new(arg),
                },
            );
        }
        cont.used = true;
        let frames = cont.frames.clone();
        let handler = cont.handler.clone();
        self.max_frame = self.max_frame.max(cont.frame_size);
        let resumed_body = plug(arg, &frames);
        StepResult::Stepped {
            term: Term::Handle {
                body: Box::new(resumed_body),
                handler,
            },
            rule: Rule::Resume,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    Stepped { term: Term, rule: Rule },
    Stuck(Outcome, Term),
}

fn term_mentions_var(term: &Term, name: &str) -> bool {
    match term {
        Term::Var(var) => var == name,
        Term::Unit | Term::Zero | Term::Cont(_) | Term::Array(_) => false,
        Term::Succ(inner)
        | Term::Perform(_, inner)
        | Term::ArrayLen(inner)
        | Term::Move(inner)
        | Term::Inplace(inner)
        | Term::Freeze(inner)
        | Term::Mark(_, inner) => term_mentions_var(inner, name),
        Term::MkArray(len, fill) | Term::ArrayGet(len, fill) => {
            term_mentions_var(len, name) || term_mentions_var(fill, name)
        }
        Term::ArraySet(array, index, value) => {
            term_mentions_var(array, name)
                || term_mentions_var(index, name)
                || term_mentions_var(value, name)
        }
        Term::Lam { param, body, .. } => param != name && term_mentions_var(body, name),
        Term::App(fun, arg) => term_mentions_var(fun, name) || term_mentions_var(arg, name),
        Term::Let { var, expr, body } => {
            term_mentions_var(expr, name) || (var != name && term_mentions_var(body, name))
        }
        Term::Fix {
            func, param, body, ..
        } => func != name && param != name && term_mentions_var(body, name),
        Term::FixGroup { bindings, .. } => {
            !bindings.iter().any(|binding| binding.func == name)
                && bindings
                    .iter()
                    .any(|binding| binding.param != name && term_mentions_var(&binding.body, name))
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } => {
            term_mentions_var(scrutinee, name)
                || term_mentions_var(zero_body, name)
                || (succ_var != name && term_mentions_var(succ_body, name))
        }
        Term::Handle { body, handler } => {
            term_mentions_var(body, name)
                || (handler.return_var != name && term_mentions_var(&handler.return_body, name))
                || handler.clauses.iter().any(|clause| {
                    clause.op_param != name
                        && clause.op_k != name
                        && term_mentions_var(&clause.op_body, name)
                })
        }
        Term::Resume { kont, arg } => term_mentions_var(kont, name) || term_mentions_var(arg, name),
    }
}

struct CapturedPerform {
    label: Label,
    arg: Term,
    frames: Vec<Frame>,
}

fn decompose_perform(term: &Term) -> Option<CapturedPerform> {
    decompose(term, Vec::new())
}

fn decompose(term: &Term, frames: Vec<Frame>) -> Option<CapturedPerform> {
    match term {
        Term::Perform(label, arg) if arg.is_value() => Some(CapturedPerform {
            label: *label,
            arg: (**arg).clone(),
            frames,
        }),
        Term::Perform(label, arg) => {
            let mut next = frames;
            next.push(Frame::Perform(*label));
            decompose(arg, next)
        }
        Term::MkArray(len, fill) if !len.is_value() => {
            let mut next = frames;
            next.push(Frame::MkArrayLen(fill.clone()));
            decompose(len, next)
        }
        Term::MkArray(len, fill) if !fill.is_value() => {
            let mut next = frames;
            next.push(Frame::MkArrayFill(len.clone()));
            decompose(fill, next)
        }
        Term::ArrayGet(array, index) if !array.is_value() => {
            let mut next = frames;
            next.push(Frame::ArrayGetArray(index.clone()));
            decompose(array, next)
        }
        Term::ArrayGet(array, index) if !index.is_value() => {
            let mut next = frames;
            next.push(Frame::ArrayGetIndex(array.clone()));
            decompose(index, next)
        }
        Term::ArraySet(array, index, value) if !array.is_value() => {
            let mut next = frames;
            next.push(Frame::ArraySetArray(index.clone(), value.clone()));
            decompose(array, next)
        }
        Term::ArraySet(array, index, value) if !index.is_value() => {
            let mut next = frames;
            next.push(Frame::ArraySetIndex(array.clone(), value.clone()));
            decompose(index, next)
        }
        Term::ArraySet(array, index, value) if !value.is_value() => {
            let mut next = frames;
            next.push(Frame::ArraySetValue(array.clone(), index.clone()));
            decompose(value, next)
        }
        Term::ArrayLen(array) if !array.is_value() => {
            let mut next = frames;
            next.push(Frame::ArrayLen);
            decompose(array, next)
        }
        Term::Move(inner) if !inner.is_value() => {
            let mut next = frames;
            next.push(Frame::Move);
            decompose(inner, next)
        }
        Term::Inplace(inner) if !inner.is_value() => {
            let mut next = frames;
            next.push(Frame::Inplace);
            decompose(inner, next)
        }
        Term::Freeze(inner) if !inner.is_value() => {
            let mut next = frames;
            next.push(Frame::Freeze);
            decompose(inner, next)
        }
        Term::Succ(inner) if !inner.is_value() => {
            let mut next = frames;
            next.push(Frame::Succ);
            decompose(inner, next)
        }
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_var,
            succ_body,
        } if !scrutinee.is_value() => {
            let mut next = frames;
            next.push(Frame::CaseNat {
                zero_body: zero_body.clone(),
                succ_var: succ_var.clone(),
                succ_body: succ_body.clone(),
            });
            decompose(scrutinee, next)
        }
        Term::App(fun, arg) if !fun.is_value() => {
            let mut next = frames;
            next.push(Frame::AppFun(arg.clone()));
            decompose(fun, next)
        }
        Term::App(fun, arg) if !arg.is_value() => {
            let mut next = frames;
            next.push(Frame::AppArg(fun.clone()));
            decompose(arg, next)
        }
        Term::Let { var, expr, body } if !expr.is_value() => {
            let mut next = frames;
            next.push(Frame::Let {
                var: var.clone(),
                body: body.clone(),
            });
            decompose(expr, next)
        }
        Term::Resume { kont, arg } if !kont.is_value() => {
            let mut next = frames;
            next.push(Frame::ResumeKont(arg.clone()));
            decompose(kont, next)
        }
        Term::Resume { kont, arg } if !arg.is_value() => {
            let mut next = frames;
            next.push(Frame::ResumeArg(kont.clone()));
            decompose(arg, next)
        }
        // Multi-label `H-op` (`calculus.md §5`, Sprint 08): a nested handler is a
        // delimiter only for labels it handles. Handlers over other labels are transparent
        // to the search and become part of the captured context.
        Term::Handle { body, handler } => {
            let mut next = frames;
            next.push(Frame::Handle(handler.clone()));
            let captured = decompose(body, next)?;
            if handler.clause_for(captured.label).is_some() {
                None
            } else {
                Some(captured)
            }
        }
        _ => None,
    }
}

fn plug(mut term: Term, frames: &[Frame]) -> Term {
    for frame in frames.iter().rev() {
        term = match frame {
            Frame::AppFun(arg) => Term::App(Box::new(term), arg.clone()),
            Frame::AppArg(fun) => Term::App(fun.clone(), Box::new(term)),
            Frame::Let { var, body } => Term::Let {
                var: var.clone(),
                expr: Box::new(term),
                body: body.clone(),
            },
            Frame::Perform(label) => Term::Perform(*label, Box::new(term)),
            Frame::MkArrayLen(fill) => Term::MkArray(Box::new(term), fill.clone()),
            Frame::MkArrayFill(len) => Term::MkArray(len.clone(), Box::new(term)),
            Frame::ArrayGetArray(index) => Term::ArrayGet(Box::new(term), index.clone()),
            Frame::ArrayGetIndex(array) => Term::ArrayGet(array.clone(), Box::new(term)),
            Frame::ArraySetArray(index, value) => {
                Term::ArraySet(Box::new(term), index.clone(), value.clone())
            }
            Frame::ArraySetIndex(array, value) => {
                Term::ArraySet(array.clone(), Box::new(term), value.clone())
            }
            Frame::ArraySetValue(array, index) => {
                Term::ArraySet(array.clone(), index.clone(), Box::new(term))
            }
            Frame::ArrayLen => Term::ArrayLen(Box::new(term)),
            Frame::Move => Term::Move(Box::new(term)),
            Frame::Inplace => Term::Inplace(Box::new(term)),
            Frame::Freeze => Term::Freeze(Box::new(term)),
            Frame::ResumeKont(arg) => Term::Resume {
                kont: Box::new(term),
                arg: arg.clone(),
            },
            Frame::ResumeArg(kont) => Term::Resume {
                kont: kont.clone(),
                arg: Box::new(term),
            },
            Frame::Succ => Term::Succ(Box::new(term)),
            Frame::CaseNat {
                zero_body,
                succ_var,
                succ_body,
            } => Term::CaseNat {
                scrutinee: Box::new(term),
                zero_body: zero_body.clone(),
                succ_var: succ_var.clone(),
                succ_body: succ_body.clone(),
            },
            Frame::Handle(handler) => Term::Handle {
                body: Box::new(term),
                handler: handler.clone(),
            },
        };
    }
    term
}

#[must_use]
pub fn eval(term: Term, budget: usize, expect_div: bool) -> EvalReport {
    Machine::new().eval(term, budget, expect_div)
}

#[must_use]
pub fn classify_progress(term: Term) -> Outcome {
    if term.is_value() {
        return Outcome::Value;
    }
    match Machine::new().step(term) {
        StepResult::Stepped { .. } => Outcome::Stepable,
        StepResult::Stuck(outcome, _) => outcome,
    }
}

#[must_use]
pub fn has_top_level_perform(term: &Term, label: Label) -> bool {
    matches!(term, Term::Perform(found, arg) if *found == label && arg.is_value())
}

#[must_use]
pub fn fix_tag(term: &Term) -> Option<RecursionTag> {
    match term {
        Term::Fix { tag, .. } => Some(*tag),
        Term::App(fun, _) => fix_tag(fun),
        _ => None,
    }
}

fn nat_to_u64(term: &Term) -> Option<u64> {
    match term {
        Term::Zero => Some(0),
        Term::Succ(inner) => nat_to_u64(inner).map(|value| value + 1),
        _ => None,
    }
}

fn u64_to_nat(value: u64) -> Term {
    Term::nat(value)
}
