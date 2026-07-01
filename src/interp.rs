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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    Value,
    Stepable,
    StuckDoubleResume,
    StuckUnhandledOperation,
    BudgetExhaustedDiv,
    InternalMalformed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalReport {
    pub outcome: Outcome,
    pub final_term: Term,
    pub trace: Vec<Rule>,
    pub max_frame: u32,
}

impl EvalReport {
    #[must_use]
    pub fn normalized_for_determinism(&self) -> Self {
        Self {
            outcome: self.outcome.clone(),
            final_term: self.final_term.normalize_cont_ids(),
            trace: self.trace.clone(),
            max_frame: self.max_frame,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Machine {
    next_cont: u64,
    continuations: BTreeMap<u64, Continuation>,
    max_frame: u32,
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
        }
    }

    pub fn step(&mut self, term: Term) -> StepResult {
        match term {
            // `((λx. e) v) → e[x := v]` (β), `calculus.md §5`.
            Term::App(fun, arg) => self.step_app(*fun, *arg),
            // `let x = v in e → e[x := v]` (let), `calculus.md §5`.
            Term::Let { var, expr, body } => self.step_let(var, *expr, *body),
            Term::Succ(inner) => self.step_succ(*inner),
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
            Term::Perform(label, arg) => self.step_perform(label, *arg),
            Term::Handle { body, handler } => self.step_handle(*body, handler),
            // `resume κ v → κ v` if unused; otherwise stuck (`calculus.md §5`).
            Term::Resume { kont, arg } => self.step_resume(*kont, *arg),
            value_or_var => StepResult::Stuck(Outcome::InternalMalformed, value_or_var),
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
            assert_eq!(
                captured.label, handler.op_label,
                "Sprint 01 has one operation label"
            );
            let frame_size = u32::try_from(captured.frames.len()).expect("frame depth fits u32");
            self.max_frame = self.max_frame.max(frame_size);
            let id = self.alloc_continuation(captured.frames, handler.clone(), frame_size);
            let with_param = handler.op_body.subst(&handler.op_param, &captured.arg);
            let with_k = with_param.subst(&handler.op_k, &Term::Cont(id));
            // `handle E[perform ℓ v] with H → e_ℓ[p := v, k := κ]` (H-op),
            // with deep `κ = λy. handle E[y] with H`, `calculus.md §5`.
            return StepResult::Stepped {
                term: with_k,
                rule: Rule::HOp,
            };
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
        // A nested handler is a delimiter for `H-op` (`calculus.md §5` evaluation context
        // excludes handle frames), so do not inspect inside it here.
        Term::Handle { .. } => None,
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
