//! Surface-to-core elaboration for Sprint 05.
//!
//! Mappings are documented in `docs/elaboration.md`; output targets `docs/calculus.md §10`.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{Handler, OpClause, RecursionTag, Term, Type};
use crate::grade::Label;
use crate::surface::ast::{
    BinaryOp, Boundedness, Decl, Expr, ExprKind, FnDecl, HandleClause, Pattern, Program, Span,
    TypeExpr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaboratedProgram {
    pub term: Term,
    pub main: Term,
    pub spans: SpanTable,
    pub prelude: Vec<&'static str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SpanTable {
    term_spans: BTreeMap<String, Span>,
    var_spans: BTreeMap<String, Vec<Span>>,
}

impl SpanTable {
    pub fn record(&mut self, term: &Term, span: Span) {
        self.term_spans.entry(term.to_string()).or_insert(span);
        if let Term::Var(name) = term {
            self.var_spans.entry(name.clone()).or_default().push(span);
        }
    }

    #[must_use]
    pub fn span_for_term_string(&self, term: &str) -> Option<Span> {
        self.term_spans.get(term).copied()
    }

    #[must_use]
    pub fn span_for_var(&self, name: &str) -> Option<Span> {
        self.var_spans
            .get(name)
            .and_then(|spans| spans.first())
            .copied()
    }

    #[must_use]
    pub fn debug_lines(&self) -> Vec<String> {
        self.term_spans
            .iter()
            .map(|(term, span)| format!("{}..{} => {term}", span.start, span.end))
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaborateError {
    pub span: Span,
    pub message: String,
}

#[derive(Debug, Clone)]
struct FunctionSig {
    params: Vec<(String, Type)>,
}

pub fn elaborate_program(program: &Program) -> Result<ElaboratedProgram, ElaborateError> {
    let mut elaborator = Elaborator::new(program)?;
    elaborator.elaborate()
}

struct Elaborator<'a> {
    program: &'a Program,
    functions: BTreeMap<String, FunctionSig>,
    spans: SpanTable,
    prelude: BTreeSet<PreludeFn>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PreludeFn {
    Pred,
    Add,
    Sub,
    Mul,
}

impl<'a> Elaborator<'a> {
    fn new(program: &'a Program) -> Result<Self, ElaborateError> {
        let mut functions = BTreeMap::new();
        for decl in &program.decls {
            match decl {
                Decl::Fn(func) => {
                    let params = func
                        .params
                        .iter()
                        .map(|param| Ok((param.name.node.clone(), lower_type(&param.ty)?)))
                        .collect::<Result<Vec<_>, ElaborateError>>()?;
                    let _ret = lower_type(&func.ret)?;
                    functions.insert(func.name.node.clone(), FunctionSig { params });
                }
                Decl::Effect(effect) => {
                    // Multi-label reduced effects (`docs/syntax.md §6`, `calculus.md §2.2`):
                    // each declared effect contributes one `Nat -> Nat` operation named `op`.
                    if effect.op.node != "op" {
                        return Err(ElaborateError {
                            span: effect.op.span,
                            message: "reduced core supports only operation name `op`".into(),
                        });
                    }
                    if lower_type(&effect.param.ty)? != Type::Nat
                        || lower_type(&effect.ret)? != Type::Nat
                    {
                        return Err(ElaborateError {
                            span: effect.span,
                            message: "reduced core operation must be `Nat -> Nat`".into(),
                        });
                    }
                }
            }
        }
        Ok(Self {
            program,
            functions,
            spans: SpanTable::default(),
            prelude: BTreeSet::new(),
        })
    }

    fn elaborate(&mut self) -> Result<ElaboratedProgram, ElaborateError> {
        let main_decl = self
            .program
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fn(func) if func.name.node == "main" => Some(func),
                _ => None,
            })
            .next()
            .ok_or_else(|| ElaborateError {
                span: Span::new(0, 0),
                message: "expected `fn main`".into(),
            })?;

        if !main_decl.params.is_empty() {
            return Err(ElaborateError {
                span: main_decl.name.span,
                message: "`main` must take no parameters".into(),
            });
        }

        let mut env = Env::default();
        let mut bindings = Vec::new();
        let decls = self.program.decls.clone();
        for decl in decls {
            if let Decl::Fn(func) = decl {
                if func.name.node == "main" {
                    let main = self.expr(&func.body, &env)?;
                    let mut term = main.clone();
                    for (name, value) in bindings.into_iter().rev() {
                        term = self.record(
                            Term::Let {
                                var: name,
                                expr: Box::new(value),
                                body: Box::new(term),
                            },
                            func.span,
                        );
                    }
                    let injected = self.prelude_with_dependencies();
                    for prelude in injected.iter().rev().copied() {
                        term = self.record(
                            Term::Let {
                                var: prelude_name(prelude).into(),
                                expr: Box::new(prelude_term(prelude)),
                                body: Box::new(term),
                            },
                            func.span,
                        );
                    }
                    return Ok(ElaboratedProgram {
                        term,
                        main,
                        spans: self.spans.clone(),
                        prelude: injected.into_iter().map(prelude_name).collect(),
                    });
                }
                let core = self.function_value(&func, &env)?;
                env.vars.insert(func.name.node.clone());
                bindings.push((func.name.node.clone(), core));
            }
        }
        unreachable!("main declaration was found before elaboration loop");
    }

    fn function_value(&mut self, func: &FnDecl, env: &Env) -> Result<Term, ElaborateError> {
        let sig = self
            .functions
            .get(&func.name.node)
            .cloned()
            .ok_or_else(|| ElaborateError {
                span: func.name.span,
                message: "internal missing function signature".into(),
            })?;
        let recursive = expr_mentions(&func.body, &func.name.node);
        if recursive {
            if sig.params.len() != 1 || sig.params[0].1 != Type::Nat {
                return Err(ElaborateError {
                    span: func.name.span,
                    message: "recursive reduced-core functions must be unary `Nat -> ...`".into(),
                });
            }
            let tag = self.recursion_tag(&func.boundedness, &sig.params[0].0)?;
            let mut body_env = env.clone();
            body_env.vars.insert(func.name.node.clone());
            body_env.vars.insert(sig.params[0].0.clone());
            let body = self.expr(&func.body, &body_env)?;
            return Ok(self.record(
                Term::Fix {
                    func: func.name.node.clone(),
                    param: sig.params[0].0.clone(),
                    param_ty: Type::Nat,
                    body: Box::new(body),
                    tag,
                },
                func.span,
            ));
        }
        let mut body_env = env.clone();
        for (name, _) in &sig.params {
            body_env.vars.insert(name.clone());
        }
        let mut term = self.expr(&func.body, &body_env)?;
        for (name, ty) in sig.params.iter().rev() {
            term = self.record(
                Term::Lam {
                    param: name.clone(),
                    param_ty: ty.clone(),
                    body: Box::new(term),
                },
                func.span,
            );
        }
        Ok(term)
    }

    fn recursion_tag(
        &mut self,
        boundedness: &Boundedness,
        param: &str,
    ) -> Result<RecursionTag, ElaborateError> {
        match boundedness {
            Boundedness::Structural => Ok(RecursionTag::Structural),
            Boundedness::Div(_) => Ok(RecursionTag::Div),
            Boundedness::Measure(expr) => {
                match &expr.kind {
                    ExprKind::Nat(_) => {}
                    ExprKind::Var(name) if name == param => {}
                    _ => {
                        return Err(ElaborateError {
                            span: expr.span,
                            message: "measure expression must be a Nat literal or the Nat parameter in the reduced surface".into(),
                        })
                    }
                }
                Ok(RecursionTag::Measure)
            }
        }
    }

    fn expr(&mut self, expr: &Expr, env: &Env) -> Result<Term, ElaborateError> {
        let term = match &expr.kind {
            ExprKind::Unit => Term::Unit,
            ExprKind::Nat(value) => Term::nat(*value),
            ExprKind::Var(name) => {
                if name != "_" && !env.vars.contains(name) && !self.functions.contains_key(name) {
                    return Err(ElaborateError {
                        span: expr.span,
                        message: format!("unbound surface variable `{name}`"),
                    });
                }
                Term::var(name)
            }
            ExprKind::Call { callee, args } => self.call(callee, args, env, expr.span)?,
            ExprKind::Binary { op, lhs, rhs } => {
                let (prelude, name) = match op {
                    BinaryOp::Add => (PreludeFn::Add, "__atli_add"),
                    BinaryOp::Sub => (PreludeFn::Sub, "__atli_sub"),
                    BinaryOp::Mul => (PreludeFn::Mul, "__atli_mul"),
                };
                self.prelude.insert(prelude);
                Term::App(
                    Box::new(Term::App(
                        Box::new(Term::var(name)),
                        Box::new(self.expr(lhs, env)?),
                    )),
                    Box::new(self.expr(rhs, env)?),
                )
            }
            ExprKind::QualifiedCall { effect, op, args } => {
                if op != "op" {
                    return Err(ElaborateError {
                        span: expr.span,
                        message: "reduced core supports only operation name `op`".into(),
                    });
                }
                if args.len() != 1 {
                    return Err(ElaborateError {
                        span: expr.span,
                        message: "effect operation `op` expects exactly one argument".into(),
                    });
                }
                Term::Perform(Label::intern(effect), Box::new(self.expr(&args[0], env)?))
            }
            ExprKind::Pipe { lhs, rhs } => {
                let desugared = desugar_pipe((**lhs).clone(), (**rhs).clone(), expr.span)?;
                return self.expr(&desugared, env);
            }
            ExprKind::Block { bindings, result } => {
                let mut local = env.clone();
                let mut lowered_bindings = Vec::new();
                for binding in bindings {
                    let value = self.expr(&binding.expr, &local)?;
                    local.vars.insert(binding.name.node.clone());
                    lowered_bindings.push((binding.name.node.clone(), value, binding.span));
                }
                let mut lowered = self.expr(result, &local)?;
                for (name, value, binding_span) in lowered_bindings.into_iter().rev() {
                    lowered = self.record(
                        Term::Let {
                            var: name,
                            expr: Box::new(value),
                            body: Box::new(lowered),
                        },
                        binding_span.join(result.span),
                    );
                }
                lowered
            }
            ExprKind::CaseNat { scrutinee, arms } => self.case(scrutinee, arms, env, expr.span)?,
            ExprKind::Handle { body, clauses } => self.handle(body, clauses, env, expr.span)?,
        };
        Ok(self.record(term, expr.span))
    }

    fn prelude_with_dependencies(&self) -> Vec<PreludeFn> {
        let mut needed = self.prelude.clone();
        if needed.contains(&PreludeFn::Sub) {
            needed.insert(PreludeFn::Pred);
        }
        if needed.contains(&PreludeFn::Mul) {
            needed.insert(PreludeFn::Add);
        }
        [
            PreludeFn::Pred,
            PreludeFn::Add,
            PreludeFn::Sub,
            PreludeFn::Mul,
        ]
        .into_iter()
        .filter(|prelude| needed.contains(prelude))
        .collect()
    }

    fn call(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        if matches!(&callee.kind, ExprKind::Var(name) if env.cont_vars.contains(name)) {
            if args.len() != 1 {
                return Err(ElaborateError {
                    span,
                    message: "continuation resume expects exactly one argument".into(),
                });
            }
            return Ok(Term::Resume {
                kont: Box::new(self.expr(callee, env)?),
                arg: Box::new(self.expr(&args[0], env)?),
            });
        }
        let mut out = self.expr(callee, env)?;
        for arg in args {
            let lowered_arg = self.expr(arg, env)?;
            out = self.record(Term::App(Box::new(out), Box::new(lowered_arg)), span);
        }
        Ok(out)
    }

    fn case(
        &mut self,
        scrutinee: &Expr,
        arms: &[crate::surface::ast::CaseArm],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        if arms.len() != 2 {
            return Err(ElaborateError {
                span,
                message: "reduced Nat case requires exactly two arms: `0` and predecessor binder"
                    .into(),
            });
        }
        let zero = match &arms[0].pattern {
            Pattern::Zero(_) => &arms[0].body,
            _ => {
                return Err(ElaborateError {
                    span: arms[0].span,
                    message: "first reduced Nat case arm must be `0`".into(),
                })
            }
        };
        let (succ_var, succ_body) = match &arms[1].pattern {
            Pattern::Bind(name) => (name.node.clone(), &arms[1].body),
            _ => {
                return Err(ElaborateError {
                    span: arms[1].span,
                    message: "second reduced Nat case arm must bind the predecessor".into(),
                })
            }
        };
        let mut succ_env = env.clone();
        succ_env.vars.insert(succ_var.clone());
        Ok(Term::CaseNat {
            scrutinee: Box::new(self.expr(scrutinee, env)?),
            zero_body: Box::new(self.expr(zero, env)?),
            succ_var,
            succ_body: Box::new(self.expr(succ_body, &succ_env)?),
        })
    }

    fn handle(
        &mut self,
        body: &Expr,
        clauses: &[HandleClause],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        let mut return_clause = None;
        let mut op_clauses = Vec::new();
        for clause in clauses {
            match clause {
                HandleClause::Return { .. } => return_clause = Some(clause),
                HandleClause::Operation { .. } => op_clauses.push(clause),
            }
        }
        let Some(HandleClause::Return {
            var,
            body: return_body,
            ..
        }) = return_clause
        else {
            return Err(ElaborateError {
                span,
                message: "handler requires a return clause in the reduced surface".into(),
            });
        };
        if op_clauses.is_empty() {
            return Err(ElaborateError {
                span,
                message: "handler requires at least one operation clause in the reduced surface"
                    .into(),
            });
        }
        let mut ret_env = env.clone();
        ret_env.vars.insert(var.node.clone());
        let mut core_clauses = Vec::new();
        for clause in op_clauses {
            let HandleClause::Operation {
                effect,
                op,
                param,
                kont,
                body: op_body,
                ..
            } = clause
            else {
                unreachable!("operation clause vector contains only operation clauses");
            };
            if op.node != "op" {
                return Err(ElaborateError {
                    span: op.span,
                    message: "reduced core supports only operation name `op`".into(),
                });
            }
            let op_param = pattern_binder(param, "_p")?;
            let op_k = pattern_binder(kont, "_k")?;
            let mut op_env = env.clone();
            op_env.vars.insert(op_param.clone());
            if op_k != "_k" {
                op_env.vars.insert(op_k.clone());
                op_env.cont_vars.insert(op_k.clone());
            }
            core_clauses.push(OpClause {
                op_label: Label::intern(&effect.node),
                op_param,
                op_k,
                op_body: Box::new(self.expr(op_body, &op_env)?),
            });
        }
        Ok(Term::Handle {
            body: Box::new(self.expr(body, env)?),
            handler: Handler {
                return_var: var.node.clone(),
                return_body: Box::new(self.expr(return_body, &ret_env)?),
                clauses: core_clauses,
            },
        })
    }

    fn record(&mut self, term: Term, span: Span) -> Term {
        self.spans.record(&term, span);
        term
    }
}

#[derive(Debug, Clone, Default)]
struct Env {
    vars: BTreeSet<String>,
    cont_vars: BTreeSet<String>,
}

fn prelude_name(prelude: PreludeFn) -> &'static str {
    match prelude {
        PreludeFn::Pred => "__atli_pred",
        PreludeFn::Add => "__atli_add",
        PreludeFn::Sub => "__atli_sub",
        PreludeFn::Mul => "__atli_mul",
    }
}

fn prelude_term(prelude: PreludeFn) -> Term {
    match prelude {
        PreludeFn::Pred => lam(
            "n",
            Term::CaseNat {
                scrutinee: Box::new(Term::var("n")),
                zero_body: Box::new(Term::zero()),
                succ_var: "p".into(),
                succ_body: Box::new(Term::var("p")),
            },
        ),
        PreludeFn::Add => lam(
            "a",
            Term::Fix {
                func: "__atli_add_loop".into(),
                param: "b".into(),
                param_ty: Type::Nat,
                body: Box::new(Term::CaseNat {
                    scrutinee: Box::new(Term::var("b")),
                    zero_body: Box::new(Term::var("a")),
                    succ_var: "q".into(),
                    succ_body: Box::new(Term::Succ(Box::new(Term::App(
                        Box::new(Term::var("__atli_add_loop")),
                        Box::new(Term::var("q")),
                    )))),
                }),
                tag: RecursionTag::Structural,
            },
        ),
        PreludeFn::Sub => lam(
            "a",
            Term::Fix {
                func: "__atli_sub_loop".into(),
                param: "b".into(),
                param_ty: Type::Nat,
                body: Box::new(Term::CaseNat {
                    scrutinee: Box::new(Term::var("b")),
                    zero_body: Box::new(Term::var("a")),
                    succ_var: "q".into(),
                    succ_body: Box::new(Term::App(
                        Box::new(Term::var("__atli_pred")),
                        Box::new(Term::App(
                            Box::new(Term::var("__atli_sub_loop")),
                            Box::new(Term::var("q")),
                        )),
                    )),
                }),
                tag: RecursionTag::Structural,
            },
        ),
        PreludeFn::Mul => lam(
            "a",
            Term::Fix {
                func: "__atli_mul_loop".into(),
                param: "b".into(),
                param_ty: Type::Nat,
                body: Box::new(Term::CaseNat {
                    scrutinee: Box::new(Term::var("b")),
                    zero_body: Box::new(Term::zero()),
                    succ_var: "q".into(),
                    succ_body: Box::new(Term::App(
                        Box::new(Term::App(
                            Box::new(Term::var("__atli_add")),
                            Box::new(Term::var("a")),
                        )),
                        Box::new(Term::App(
                            Box::new(Term::var("__atli_mul_loop")),
                            Box::new(Term::var("q")),
                        )),
                    )),
                }),
                tag: RecursionTag::Structural,
            },
        ),
    }
}

fn lam(param: &str, body: Term) -> Term {
    Term::Lam {
        param: param.into(),
        param_ty: Type::Nat,
        body: Box::new(body),
    }
}

fn lower_type(ty: &TypeExpr) -> Result<Type, ElaborateError> {
    match ty {
        TypeExpr::Unit(_) => Ok(Type::Unit),
        TypeExpr::Nat(_) => Ok(Type::Nat),
        TypeExpr::Arrow(arg, ret, _) => Ok(Type::Arrow(
            Box::new(lower_type(arg)?),
            Box::new(lower_type(ret)?),
        )),
    }
}

fn pattern_binder(pattern: &Pattern, fallback: &str) -> Result<String, ElaborateError> {
    match pattern {
        Pattern::Bind(name) => Ok(name.node.clone()),
        Pattern::Wildcard(_) => Ok(fallback.into()),
        Pattern::Zero(span) => Err(ElaborateError {
            span: *span,
            message: "operation clause binders must be names or `_`".into(),
        }),
    }
}

fn desugar_pipe(lhs: Expr, rhs: Expr, span: Span) -> Result<Expr, ElaborateError> {
    match rhs.kind {
        ExprKind::Call { callee, mut args } => {
            args.insert(0, lhs);
            Ok(Expr::new(ExprKind::Call { callee, args }, span))
        }
        ExprKind::Var(_) => Ok(Expr::new(
            ExprKind::Call {
                callee: Box::new(rhs),
                args: vec![lhs],
            },
            span,
        )),
        _ => Err(ElaborateError {
            span: rhs.span,
            message: "pipe RHS must be a function call or function name in the reduced surface"
                .into(),
        }),
    }
}

fn expr_mentions(expr: &Expr, name: &str) -> bool {
    match &expr.kind {
        ExprKind::Var(found) => found == name,
        ExprKind::Unit | ExprKind::Nat(_) => false,
        ExprKind::Call { callee, args } => {
            expr_mentions(callee, name) || args.iter().any(|arg| expr_mentions(arg, name))
        }
        ExprKind::QualifiedCall { args, .. } => args.iter().any(|arg| expr_mentions(arg, name)),
        ExprKind::Binary { lhs, rhs, .. } => expr_mentions(lhs, name) || expr_mentions(rhs, name),
        ExprKind::Pipe { lhs, rhs } => expr_mentions(lhs, name) || expr_mentions(rhs, name),
        ExprKind::Block { bindings, result } => {
            bindings
                .iter()
                .any(|binding| expr_mentions(&binding.expr, name))
                || expr_mentions(result, name)
        }
        ExprKind::CaseNat { scrutinee, arms } => {
            expr_mentions(scrutinee, name) || arms.iter().any(|arm| expr_mentions(&arm.body, name))
        }
        ExprKind::Handle { body, clauses } => {
            expr_mentions(body, name)
                || clauses.iter().any(|clause| match clause {
                    HandleClause::Return { body, .. } | HandleClause::Operation { body, .. } => {
                        expr_mentions(body, name)
                    }
                })
        }
    }
}
