//! Surface-to-core elaboration for Sprint 05.
//!
//! Mappings are documented in `docs/elaboration.md`; output targets `docs/calculus.md §10`.

use std::collections::{BTreeMap, BTreeSet};

use crate::core::{CoverageTag, FixBinding, Handler, OpClause, RecursionTag, Term, Type};
use crate::grade::{Label, Q};
use crate::surface::ast::{
    BinaryOp, Boundedness, Decl, Expr, ExprKind, FnDecl, HandleClause, Pattern, PrefixOp, Program,
    Span, TypeDeclKind, TypeExpr,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParamMode {
    Shared,
    Unique,
    Preserve,
}

#[derive(Debug, Clone)]
struct FunctionSig {
    params: Vec<(String, Type, ParamMode)>,
}

pub fn elaborate_program(program: &Program) -> Result<ElaboratedProgram, ElaborateError> {
    check_surface_types(program)?;
    check_surface_uniqueness(program)?;
    let mut elaborator = Elaborator::new(program)?;
    elaborator.elaborate()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SurfaceTy {
    Unit,
    Nat,
    Named(String, Vec<SurfaceTy>),
    Var(u32, String),
    Arrow(Box<SurfaceTy>, Box<SurfaceTy>),
}

impl std::fmt::Display for SurfaceTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => f.write_str("Unit"),
            Self::Nat => f.write_str("Nat"),
            Self::Named(name, args) if args.is_empty() => f.write_str(name),
            Self::Named(name, args) => {
                let args = args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{name}[{args}]")
            }
            Self::Var(_, name) => f.write_str(name),
            Self::Arrow(arg, ret) => write!(f, "{arg} -> {ret}"),
        }
    }
}

#[derive(Default)]
struct TypeInfer {
    next: u32,
    subst: BTreeMap<u32, SurfaceTy>,
}

impl TypeInfer {
    fn fresh(&mut self, name: &str) -> SurfaceTy {
        let id = self.next;
        self.next += 1;
        SurfaceTy::Var(id, name.into())
    }

    fn resolve(&mut self, ty: SurfaceTy) -> SurfaceTy {
        match ty {
            SurfaceTy::Var(id, name) => {
                if let Some(bound) = self.subst.get(&id).cloned() {
                    self.resolve(bound)
                } else {
                    SurfaceTy::Var(id, name)
                }
            }
            SurfaceTy::Named(name, args) => SurfaceTy::Named(
                name,
                args.into_iter().map(|arg| self.resolve(arg)).collect(),
            ),
            SurfaceTy::Arrow(arg, ret) => {
                SurfaceTy::Arrow(Box::new(self.resolve(*arg)), Box::new(self.resolve(*ret)))
            }
            other => other,
        }
    }

    fn unify(&mut self, lhs: SurfaceTy, rhs: SurfaceTy, span: Span) -> Result<(), ElaborateError> {
        let lhs = self.resolve(lhs);
        let rhs = self.resolve(rhs);
        match (lhs, rhs) {
            (SurfaceTy::Var(lhs, _), SurfaceTy::Var(rhs, _)) if lhs == rhs => Ok(()),
            (SurfaceTy::Var(id, _), ty) | (ty, SurfaceTy::Var(id, _)) => {
                self.subst.insert(id, ty);
                Ok(())
            }
            (SurfaceTy::Unit, SurfaceTy::Unit) | (SurfaceTy::Nat, SurfaceTy::Nat) => Ok(()),
            // Generic arrow-position instantiation (`docs/calculus.md §4`, Sprint 14):
            // recurse structurally so `A -> B` binds from a passed function's arrow type.
            (SurfaceTy::Arrow(a1, r1), SurfaceTy::Arrow(a2, r2)) => {
                self.unify(*a1, *a2, span)?;
                self.unify(*r1, *r2, span)
            }
            (SurfaceTy::Named(n1, a1), SurfaceTy::Named(n2, a2))
                if n1 == n2 && a1.len() == a2.len() =>
            {
                for (lhs, rhs) in a1.into_iter().zip(a2) {
                    self.unify(lhs, rhs, span)?;
                }
                Ok(())
            }
            (found, expected) => Err(ElaborateError {
                span,
                message: format!("type mismatch: expected `{expected}`, found `{found}`"),
            }),
        }
    }
}

#[derive(Debug, Clone)]
struct SurfaceFnSig {
    type_params: Vec<String>,
    params: Vec<(String, TypeExpr)>,
    ret: TypeExpr,
}

#[derive(Debug, Clone)]
struct SurfaceCtorSig {
    owner: String,
    owner_params: Vec<String>,
    payloads: Vec<TypeExpr>,
}

#[derive(Debug, Clone)]
struct SurfaceFieldSig {
    owner: String,
    owner_params: Vec<String>,
    ty: TypeExpr,
}

#[derive(Default)]
struct SurfaceTypeCtx {
    functions: BTreeMap<String, SurfaceFnSig>,
    constructors: BTreeMap<String, SurfaceCtorSig>,
    records: BTreeMap<String, Vec<(String, TypeExpr)>>,
    fields: BTreeMap<String, SurfaceFieldSig>,
}

struct Elaborator<'a> {
    program: &'a Program,
    functions: BTreeMap<String, FunctionSig>,
    aggregates: AggregateEnv,
    spans: SpanTable,
    prelude: BTreeSet<PreludeFn>,
}

#[derive(Debug, Clone, Default)]
struct AggregateEnv {
    records: BTreeMap<String, Vec<(String, TypeExpr)>>,
    constructors: BTreeMap<String, ConstructorInfo>,
    fields: BTreeMap<String, FieldInfo>,
}

#[derive(Debug, Clone)]
struct ConstructorInfo {
    type_name: String,
    tag: u64,
    payloads: Vec<TypeExpr>,
    payload_count: usize,
    slot_count: usize,
}

#[derive(Debug, Clone)]
struct FieldInfo {
    index: usize,
    ty: TypeExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PreludeFn {
    Pred,
    Add,
    Sub,
    Mul,
}

fn validate_type_uses(program: &Program) -> Result<(), ElaborateError> {
    let mut arities = BTreeMap::new();
    for decl in &program.decls {
        if let Decl::Type(decl) = decl {
            arities.insert(decl.name.node.clone(), decl.type_params.len());
        }
    }
    for decl in &program.decls {
        match decl {
            Decl::Type(decl) => {
                let params = decl
                    .type_params
                    .iter()
                    .map(|param| param.node.clone())
                    .collect::<BTreeSet<_>>();
                match &decl.kind {
                    TypeDeclKind::Record(fields) => {
                        for field in fields {
                            validate_type_expr(&field.ty, &params, &arities)?;
                        }
                    }
                    TypeDeclKind::Variant(ctors) => {
                        for ctor in ctors {
                            for payload in &ctor.payloads {
                                validate_type_expr(payload, &params, &arities)?;
                            }
                        }
                    }
                }
            }
            Decl::Fn(func) => {
                let params = func
                    .type_params
                    .iter()
                    .map(|param| param.node.clone())
                    .collect::<BTreeSet<_>>();
                for param in &func.params {
                    validate_type_expr(&param.ty, &params, &arities)?;
                }
                validate_type_expr(&func.ret, &params, &arities)?;
            }
            Decl::Effect(effect) => {
                let params = BTreeSet::new();
                validate_type_expr(&effect.param.ty, &params, &arities)?;
                validate_type_expr(&effect.ret, &params, &arities)?;
            }
        }
    }
    Ok(())
}

fn check_surface_types(program: &Program) -> Result<(), ElaborateError> {
    validate_type_uses(program)?;
    let ctx = SurfaceTypeCtx::from_program(program);
    for decl in &program.decls {
        let Decl::Fn(func) = decl else {
            continue;
        };
        let mut infer = TypeInfer::default();
        let mut locals = BTreeMap::new();
        let type_params = func
            .type_params
            .iter()
            .map(|param| param.node.clone())
            .collect::<BTreeSet<_>>();
        for param in &func.params {
            locals.insert(
                param.name.node.clone(),
                surface_ty_from_expr(&param.ty, &type_params, &mut infer),
            );
        }
        let found = infer_surface_expr(&func.body, &ctx, &mut locals, &mut infer)?;
        let expected = surface_ty_from_expr(&func.ret, &type_params, &mut infer);
        infer.unify(found, expected, func.ret.span())?;
    }
    Ok(())
}

impl SurfaceTypeCtx {
    fn from_program(program: &Program) -> Self {
        let mut ctx = Self::default();
        for decl in &program.decls {
            match decl {
                Decl::Fn(func) => {
                    ctx.functions.insert(
                        func.name.node.clone(),
                        SurfaceFnSig {
                            type_params: func
                                .type_params
                                .iter()
                                .map(|param| param.node.clone())
                                .collect(),
                            params: func
                                .params
                                .iter()
                                .map(|param| (param.name.node.clone(), param.ty.clone()))
                                .collect(),
                            ret: func.ret.clone(),
                        },
                    );
                }
                Decl::Type(decl) => match &decl.kind {
                    TypeDeclKind::Variant(ctors) => {
                        let owner_params = decl
                            .type_params
                            .iter()
                            .map(|param| param.node.clone())
                            .collect::<Vec<_>>();
                        for ctor in ctors {
                            ctx.constructors.insert(
                                ctor.name.node.clone(),
                                SurfaceCtorSig {
                                    owner: decl.name.node.clone(),
                                    owner_params: owner_params.clone(),
                                    payloads: ctor.payloads.clone(),
                                },
                            );
                        }
                    }
                    TypeDeclKind::Record(fields) => {
                        let owner_params = decl
                            .type_params
                            .iter()
                            .map(|param| param.node.clone())
                            .collect::<Vec<_>>();
                        for field in fields {
                            ctx.fields.insert(
                                field.name.node.clone(),
                                SurfaceFieldSig {
                                    owner: decl.name.node.clone(),
                                    owner_params: owner_params.clone(),
                                    ty: field.ty.clone(),
                                },
                            );
                        }
                        ctx.records.insert(
                            decl.name.node.clone(),
                            fields
                                .iter()
                                .map(|field| (field.name.node.clone(), field.ty.clone()))
                                .collect(),
                        );
                    }
                },
                Decl::Effect(_) => {}
            }
        }
        ctx
    }

    fn record_for_fields(
        &self,
        fields: &[(crate::surface::ast::Spanned<String>, Expr)],
    ) -> Option<String> {
        let names = fields
            .iter()
            .map(|(name, _)| name.node.as_str())
            .collect::<BTreeSet<_>>();
        self.records.iter().find_map(|(record, declared)| {
            let declared_names = declared
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<BTreeSet<_>>();
            (declared_names == names).then(|| record.clone())
        })
    }
}

fn surface_ty_from_expr(
    ty: &TypeExpr,
    type_params: &BTreeSet<String>,
    infer: &mut TypeInfer,
) -> SurfaceTy {
    match ty {
        TypeExpr::Unit(_) => SurfaceTy::Unit,
        TypeExpr::Nat(_) => SurfaceTy::Nat,
        TypeExpr::Array(_) => SurfaceTy::Named("Array".into(), vec![SurfaceTy::Nat]),
        TypeExpr::Named(name, _) if type_params.contains(name) => infer.fresh(name),
        TypeExpr::Named(name, _) => SurfaceTy::Named(name.clone(), Vec::new()),
        TypeExpr::Applied(name, args, _) => SurfaceTy::Named(
            name.clone(),
            args.iter()
                .map(|arg| surface_ty_from_expr(arg, type_params, infer))
                .collect(),
        ),
        TypeExpr::Unique(inner, _) | TypeExpr::Preserve { inner, .. } => {
            surface_ty_from_expr(inner, type_params, infer)
        }
        TypeExpr::Arrow(arg, ret, _) => SurfaceTy::Arrow(
            Box::new(surface_ty_from_expr(arg, type_params, infer)),
            Box::new(surface_ty_from_expr(ret, type_params, infer)),
        ),
    }
}

fn instantiate_type(ty: &TypeExpr, params: &BTreeMap<String, SurfaceTy>) -> SurfaceTy {
    match ty {
        TypeExpr::Unit(_) => SurfaceTy::Unit,
        TypeExpr::Nat(_) => SurfaceTy::Nat,
        TypeExpr::Array(_) => SurfaceTy::Named("Array".into(), vec![SurfaceTy::Nat]),
        TypeExpr::Named(name, _) => params
            .get(name)
            .cloned()
            .unwrap_or_else(|| SurfaceTy::Named(name.clone(), Vec::new())),
        TypeExpr::Applied(name, args, _) => SurfaceTy::Named(
            name.clone(),
            args.iter()
                .map(|arg| instantiate_type(arg, params))
                .collect(),
        ),
        TypeExpr::Unique(inner, _) | TypeExpr::Preserve { inner, .. } => {
            instantiate_type(inner, params)
        }
        TypeExpr::Arrow(arg, ret, _) => SurfaceTy::Arrow(
            Box::new(instantiate_type(arg, params)),
            Box::new(instantiate_type(ret, params)),
        ),
    }
}

fn instantiate_fn(sig: &SurfaceFnSig, infer: &mut TypeInfer) -> (Vec<SurfaceTy>, SurfaceTy) {
    let params = sig
        .type_params
        .iter()
        .map(|name| (name.clone(), infer.fresh(name)))
        .collect::<BTreeMap<_, _>>();
    let args = sig
        .params
        .iter()
        .map(|(_, ty)| instantiate_type(ty, &params))
        .collect();
    let ret = instantiate_type(&sig.ret, &params);
    (args, ret)
}

fn instantiate_constructor(
    ctor: &SurfaceCtorSig,
    infer: &mut TypeInfer,
) -> (Vec<SurfaceTy>, SurfaceTy) {
    let params = ctor
        .owner_params
        .iter()
        .map(|name| (name.clone(), infer.fresh(name)))
        .collect::<BTreeMap<_, _>>();
    let payloads = ctor
        .payloads
        .iter()
        .map(|ty| instantiate_type(ty, &params))
        .collect::<Vec<_>>();
    let result = SurfaceTy::Named(
        ctor.owner.clone(),
        ctor.owner_params
            .iter()
            .map(|name| params.get(name).cloned().unwrap())
            .collect(),
    );
    (payloads, result)
}

fn instantiate_field(field: &SurfaceFieldSig, infer: &mut TypeInfer) -> (SurfaceTy, SurfaceTy) {
    let params = field
        .owner_params
        .iter()
        .map(|name| (name.clone(), infer.fresh(name)))
        .collect::<BTreeMap<_, _>>();
    let owner = SurfaceTy::Named(
        field.owner.clone(),
        field
            .owner_params
            .iter()
            .map(|name| params.get(name).cloned().unwrap())
            .collect(),
    );
    let ty = instantiate_type(&field.ty, &params);
    (owner, ty)
}

fn fn_type_from_sig(sig: &SurfaceFnSig, infer: &mut TypeInfer) -> SurfaceTy {
    let (params, ret) = instantiate_fn(sig, infer);
    params.into_iter().rev().fold(ret, |acc, param| {
        SurfaceTy::Arrow(Box::new(param), Box::new(acc))
    })
}

fn infer_surface_expr(
    expr: &Expr,
    ctx: &SurfaceTypeCtx,
    locals: &mut BTreeMap<String, SurfaceTy>,
    infer: &mut TypeInfer,
) -> Result<SurfaceTy, ElaborateError> {
    match &expr.kind {
        ExprKind::Unit => Ok(SurfaceTy::Unit),
        ExprKind::Nat(_) => Ok(SurfaceTy::Nat),
        ExprKind::Var(name) => {
            if let Some(local) = locals.get(name).cloned() {
                return Ok(local);
            }
            if let Some(sig) = ctx.functions.get(name) {
                return Ok(fn_type_from_sig(sig, infer));
            }
            if let Some(ctor) = ctx.constructors.get(name) {
                let (payloads, result) = instantiate_constructor(ctor, infer);
                if payloads.is_empty() {
                    return Ok(result);
                }
            }
            Ok(SurfaceTy::Nat)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            let lhs_ty = infer_surface_expr(lhs, ctx, locals, infer)?;
            let rhs_ty = infer_surface_expr(rhs, ctx, locals, infer)?;
            infer.unify(lhs_ty, SurfaceTy::Nat, lhs.span)?;
            infer.unify(rhs_ty, SurfaceTy::Nat, rhs.span)?;
            Ok(SurfaceTy::Nat)
        }
        ExprKind::Pipe { lhs, rhs } => {
            let desugared = desugar_pipe((**lhs).clone(), (**rhs).clone(), expr.span)?;
            infer_surface_expr(&desugared, ctx, locals, infer)
        }
        ExprKind::Prefix { expr: inner, .. } => infer_surface_expr(inner, ctx, locals, infer),
        ExprKind::Block { bindings, result } => {
            let mut inner = locals.clone();
            for binding in bindings {
                let ty = infer_surface_expr(&binding.expr, ctx, &mut inner, infer)?;
                inner.insert(binding.name.node.clone(), infer.resolve(ty));
            }
            infer_surface_expr(result, ctx, &mut inner, infer)
        }
        ExprKind::Call { callee, args } => {
            if let ExprKind::Var(name) = &callee.kind {
                if let Some(ctor) = ctx.constructors.get(name) {
                    let (params, ret) = instantiate_constructor(ctor, infer);
                    if params.len() != args.len() {
                        return Err(ElaborateError {
                            span: expr.span,
                            message: format!(
                                "constructor `{name}` expects {} payloads",
                                params.len()
                            ),
                        });
                    }
                    for (arg, expected) in args.iter().zip(params) {
                        let found = infer_surface_expr(arg, ctx, locals, infer)?;
                        infer.unify(found, expected, arg.span)?;
                    }
                    return Ok(infer.resolve(ret));
                }
                match name.as_str() {
                    "mkarray" if args.len() == 2 => {
                        let len = infer_surface_expr(&args[0], ctx, locals, infer)?;
                        infer.unify(len, SurfaceTy::Nat, args[0].span)?;
                        let elem = infer_surface_expr(&args[1], ctx, locals, infer)?;
                        return Ok(SurfaceTy::Named("Array".into(), vec![infer.resolve(elem)]));
                    }
                    "get" if args.len() == 2 => {
                        let elem = infer.fresh("A");
                        let arr = infer_surface_expr(&args[0], ctx, locals, infer)?;
                        let idx = infer_surface_expr(&args[1], ctx, locals, infer)?;
                        infer.unify(
                            arr,
                            SurfaceTy::Named("Array".into(), vec![elem.clone()]),
                            args[0].span,
                        )?;
                        infer.unify(idx, SurfaceTy::Nat, args[1].span)?;
                        return Ok(infer.resolve(elem));
                    }
                    "set" if args.len() == 3 => {
                        let elem = infer.fresh("A");
                        let arr = infer_surface_expr(&args[0], ctx, locals, infer)?;
                        let idx = infer_surface_expr(&args[1], ctx, locals, infer)?;
                        let val = infer_surface_expr(&args[2], ctx, locals, infer)?;
                        infer.unify(
                            arr,
                            SurfaceTy::Named("Array".into(), vec![elem.clone()]),
                            args[0].span,
                        )?;
                        infer.unify(idx, SurfaceTy::Nat, args[1].span)?;
                        infer.unify(val, elem.clone(), args[2].span)?;
                        return Ok(SurfaceTy::Named("Array".into(), vec![infer.resolve(elem)]));
                    }
                    "len" if args.len() == 1 => {
                        let elem = infer.fresh("A");
                        let arr = infer_surface_expr(&args[0], ctx, locals, infer)?;
                        infer.unify(
                            arr,
                            SurfaceTy::Named("Array".into(), vec![elem]),
                            args[0].span,
                        )?;
                        return Ok(SurfaceTy::Nat);
                    }
                    _ => {}
                }
                if let Some(sig) = ctx.functions.get(name) {
                    let (params, ret) = instantiate_fn(sig, infer);
                    if params.len() != args.len() {
                        return Err(ElaborateError {
                            span: expr.span,
                            message: format!(
                                "function `{name}` expects {} argument(s)",
                                params.len()
                            ),
                        });
                    }
                    for (arg, expected) in args.iter().zip(params) {
                        let found = infer_surface_expr(arg, ctx, locals, infer)?;
                        infer.unify(found, expected, arg.span)?;
                    }
                    return Ok(infer.resolve(ret));
                }
            }
            let mut fun = infer_surface_expr(callee, ctx, locals, infer)?;
            for arg in args {
                let arg_ty = infer_surface_expr(arg, ctx, locals, infer)?;
                let ret = infer.fresh("R");
                infer.unify(
                    fun,
                    SurfaceTy::Arrow(Box::new(arg_ty), Box::new(ret.clone())),
                    expr.span,
                )?;
                fun = infer.resolve(ret);
            }
            Ok(fun)
        }
        ExprKind::CaseNat { scrutinee, arms } => {
            let scrut_ty = infer_surface_expr(scrutinee, ctx, locals, infer)?;
            let is_variant = arms.iter().any(|arm| {
                matches!(
                    arm.pattern,
                    Pattern::Constructor { .. } | Pattern::Record { .. } | Pattern::Wildcard(_)
                )
            }) && !arms
                .iter()
                .any(|arm| matches!(arm.pattern, Pattern::Zero(_)));
            if is_variant {
                infer_variant_case(arms, scrut_ty, ctx, locals, infer, expr.span)
            } else {
                infer.unify(scrut_ty, SurfaceTy::Nat, scrutinee.span)?;
                let mut out = None;
                for arm in arms {
                    let mut branch_locals = locals.clone();
                    if let Pattern::Bind(name) = &arm.pattern {
                        branch_locals.insert(name.node.clone(), SurfaceTy::Nat);
                    }
                    let branch = infer_surface_expr(&arm.body, ctx, &mut branch_locals, infer)?;
                    if let Some(prev) = out.clone() {
                        infer.unify(branch, prev, arm.body.span)?;
                    } else {
                        out = Some(branch);
                    }
                }
                Ok(infer.resolve(out.unwrap_or(SurfaceTy::Unit)))
            }
        }
        ExprKind::RecordLit(fields) => {
            let record = ctx
                .record_for_fields(fields)
                .ok_or_else(|| ElaborateError {
                    span: expr.span,
                    message: "record literal fields do not match a declared record type".into(),
                })?;
            let declared = ctx.records.get(&record).expect("record exists");
            let owner_params = ctx
                .fields
                .values()
                .find(|field| field.owner == record)
                .map(|field| field.owner_params.clone())
                .unwrap_or_default();
            let params = owner_params
                .iter()
                .map(|name| (name.clone(), infer.fresh(name)))
                .collect::<BTreeMap<_, _>>();
            for (field_name, field_ty) in declared {
                let (_, field_expr) = fields
                    .iter()
                    .find(|(name, _)| name.node == *field_name)
                    .expect("record_for_fields checked names");
                let found = infer_surface_expr(field_expr, ctx, locals, infer)?;
                let expected = instantiate_type(field_ty, &params);
                infer.unify(found, expected, field_expr.span)?;
            }
            Ok(SurfaceTy::Named(
                record,
                owner_params
                    .iter()
                    .map(|name| params.get(name).cloned().unwrap())
                    .collect(),
            ))
        }
        ExprKind::RecordUpdate {
            record,
            field,
            value,
        } => {
            let record_ty = infer_surface_expr(record, ctx, locals, infer)?;
            let field_sig = ctx.fields.get(&field.node).ok_or_else(|| ElaborateError {
                span: field.span,
                message: format!("unknown record field `{}`", field.node),
            })?;
            let (owner_ty, field_ty) = instantiate_field(field_sig, infer);
            infer.unify(record_ty.clone(), owner_ty, record.span)?;
            let found = infer_surface_expr(value, ctx, locals, infer)?;
            infer.unify(found, field_ty, value.span)?;
            Ok(infer.resolve(record_ty))
        }
        ExprKind::Field { record, field } => {
            let record_ty = infer_surface_expr(record, ctx, locals, infer)?;
            let field_sig = ctx.fields.get(&field.node).ok_or_else(|| ElaborateError {
                span: field.span,
                message: format!("unknown record field `{}`", field.node),
            })?;
            let (owner_ty, field_ty) = instantiate_field(field_sig, infer);
            infer.unify(record_ty, owner_ty, record.span)?;
            Ok(infer.resolve(field_ty))
        }
        ExprKind::QualifiedCall { args, .. } => {
            for arg in args {
                let found = infer_surface_expr(arg, ctx, locals, infer)?;
                infer.unify(found, SurfaceTy::Nat, arg.span)?;
            }
            Ok(SurfaceTy::Nat)
        }
        ExprKind::Handle { body, clauses } => {
            let body_ty = infer_surface_expr(body, ctx, locals, infer)?;
            for clause in clauses {
                match clause {
                    HandleClause::Return { var, body, .. } => {
                        let mut clause_locals = locals.clone();
                        clause_locals.insert(var.node.clone(), body_ty.clone());
                        let clause_ty = infer_surface_expr(body, ctx, &mut clause_locals, infer)?;
                        infer.unify(clause_ty, body_ty.clone(), body.span)?;
                    }
                    HandleClause::Operation {
                        param, kont, body, ..
                    } => {
                        let mut clause_locals = locals.clone();
                        if let Pattern::Bind(param) = param {
                            clause_locals.insert(param.node.clone(), SurfaceTy::Nat);
                        }
                        if let Pattern::Bind(kont) = kont {
                            clause_locals.insert(
                                kont.node.clone(),
                                SurfaceTy::Arrow(
                                    Box::new(SurfaceTy::Nat),
                                    Box::new(body_ty.clone()),
                                ),
                            );
                        }
                        let clause_ty = infer_surface_expr(body, ctx, &mut clause_locals, infer)?;
                        infer.unify(clause_ty, body_ty.clone(), body.span)?;
                    }
                }
            }
            Ok(body_ty)
        }
        ExprKind::Scope { body } => infer_surface_expr(body, ctx, locals, infer),
        ExprKind::Spawn { callee, args } => {
            if let Some(sig) = ctx.functions.get(&callee.node) {
                let (params, ret) = instantiate_fn(sig, infer);
                for (arg, expected) in args.iter().zip(params) {
                    let found = infer_surface_expr(arg, ctx, locals, infer)?;
                    infer.unify(found, expected, arg.span)?;
                }
                Ok(SurfaceTy::Named("Task".into(), vec![ret]))
            } else {
                Ok(SurfaceTy::Named("Task".into(), vec![SurfaceTy::Nat]))
            }
        }
        ExprKind::Await { handle } => {
            let ret = infer.fresh("T");
            let found = infer_surface_expr(handle, ctx, locals, infer)?;
            infer.unify(
                found,
                SurfaceTy::Named("Task".into(), vec![ret.clone()]),
                handle.span,
            )?;
            Ok(infer.resolve(ret))
        }
    }
}

fn infer_variant_case(
    arms: &[crate::surface::ast::CaseArm],
    scrut_ty: SurfaceTy,
    ctx: &SurfaceTypeCtx,
    locals: &mut BTreeMap<String, SurfaceTy>,
    infer: &mut TypeInfer,
    span: Span,
) -> Result<SurfaceTy, ElaborateError> {
    let mut out = None;
    for arm in arms {
        let mut branch_locals = locals.clone();
        match &arm.pattern {
            Pattern::Constructor { name, args, .. } => {
                if let Some(ctor) = ctx.constructors.get(&name.node) {
                    let (payloads, result) = instantiate_constructor(ctor, infer);
                    infer.unify(scrut_ty.clone(), result, name.span)?;
                    for (pattern, payload_ty) in args.iter().zip(payloads) {
                        if let Pattern::Bind(bind) = pattern {
                            branch_locals.insert(bind.node.clone(), payload_ty);
                        }
                    }
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    branch_locals.insert(field.node.clone(), infer.fresh("F"));
                }
            }
            Pattern::Wildcard(_) => {}
            Pattern::Zero(_) | Pattern::Bind(_) => {}
        }
        let branch = infer_surface_expr(&arm.body, ctx, &mut branch_locals, infer)?;
        if let Some(prev) = out.clone() {
            infer.unify(branch, prev, arm.body.span)?;
        } else {
            out = Some(branch);
        }
    }
    Ok(infer.resolve(out.unwrap_or_else(|| {
        let _ = span;
        SurfaceTy::Unit
    })))
}

fn validate_type_expr(
    ty: &TypeExpr,
    params: &BTreeSet<String>,
    arities: &BTreeMap<String, usize>,
) -> Result<(), ElaborateError> {
    match ty {
        TypeExpr::Unit(_) | TypeExpr::Nat(_) | TypeExpr::Array(_) => Ok(()),
        TypeExpr::Unique(inner, _) | TypeExpr::Preserve { inner, .. } => {
            validate_type_expr(inner, params, arities)
        }
        TypeExpr::Arrow(arg, ret, _) => {
            validate_type_expr(arg, params, arities)?;
            validate_type_expr(ret, params, arities)
        }
        TypeExpr::Named(name, span) => {
            if params.contains(name) || matches!(name.as_str(), "Task") {
                return Ok(());
            }
            match arities.get(name) {
                Some(0) => Ok(()),
                Some(expected) => Err(ElaborateError {
                    span: *span,
                    message: format!("type `{name}` expects {expected} type argument(s)"),
                }),
                None => Err(ElaborateError {
                    span: *span,
                    message: format!("unbound type variable `{name}`"),
                }),
            }
        }
        TypeExpr::Applied(name, args, span) => {
            for arg in args {
                validate_type_expr(arg, params, arities)?;
            }
            let expected = match name.as_str() {
                "Array" | "Task" => Some(1),
                _ => arities.get(name).copied(),
            };
            match expected {
                Some(n) if n == args.len() => Ok(()),
                Some(n) => Err(ElaborateError {
                    span: *span,
                    message: format!(
                        "type `{name}` expects {n} type argument(s), got {}",
                        args.len()
                    ),
                }),
                None => Err(ElaborateError {
                    span: *span,
                    message: format!("unknown type `{name}`"),
                }),
            }
        }
    }
}

impl AggregateEnv {
    fn from_program(program: &Program) -> Result<Self, ElaborateError> {
        let mut env = Self::default();
        for decl in &program.decls {
            let Decl::Type(decl) = decl else {
                continue;
            };
            match &decl.kind {
                TypeDeclKind::Record(fields) => {
                    let mut out = Vec::new();
                    for (idx, field) in fields.iter().enumerate() {
                        out.push((field.name.node.clone(), field.ty.clone()));
                        env.fields.insert(
                            field.name.node.clone(),
                            FieldInfo {
                                index: idx,
                                ty: field.ty.clone(),
                            },
                        );
                    }
                    env.records.insert(decl.name.node.clone(), out);
                }
                TypeDeclKind::Variant(ctors) => {
                    let slot_count = 1 + ctors
                        .iter()
                        .map(|ctor| ctor.payloads.len())
                        .max()
                        .unwrap_or(0);
                    for (tag, ctor) in ctors.iter().enumerate() {
                        env.constructors.insert(
                            ctor.name.node.clone(),
                            ConstructorInfo {
                                type_name: decl.name.node.clone(),
                                tag: u64::try_from(tag).unwrap(),
                                payloads: ctor.payloads.clone(),
                                payload_count: ctor.payloads.len(),
                                slot_count,
                            },
                        );
                    }
                }
            }
        }
        Ok(env)
    }

    fn record_for_fields(
        &self,
        fields: &[(crate::surface::ast::Spanned<String>, Expr)],
    ) -> Option<String> {
        let names = fields
            .iter()
            .map(|(name, _)| name.node.as_str())
            .collect::<BTreeSet<_>>();
        self.records.iter().find_map(|(record, declared)| {
            let declared_names = declared
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<BTreeSet<_>>();
            (declared_names == names).then(|| record.clone())
        })
    }
}

impl<'a> Elaborator<'a> {
    fn new(program: &'a Program) -> Result<Self, ElaborateError> {
        validate_type_uses(program)?;
        let aggregates = AggregateEnv::from_program(program)?;
        let mut functions = BTreeMap::new();
        for decl in &program.decls {
            match decl {
                Decl::Fn(func) => {
                    let params = func
                        .params
                        .iter()
                        .map(|param| {
                            Ok((
                                param.name.node.clone(),
                                lower_type(&param.ty)?,
                                type_mode(&param.ty),
                            ))
                        })
                        .collect::<Result<Vec<_>, ElaborateError>>()?;
                    let _ret = lower_type(&func.ret)?;
                    functions.insert(func.name.node.clone(), FunctionSig { params });
                }
                Decl::Type(_) => {}
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
            aggregates,
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

        let fn_decls: Vec<_> = self
            .program
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fn(func) if func.name.node != "main" => Some(func.clone()),
                _ => None,
            })
            .collect();
        let order = declaration_scc_order(&fn_decls);
        let mut env = Env::default();
        let mut bindings = Vec::new();
        for component in order {
            if component.len() == 1 {
                let func = &fn_decls[component[0]];
                let core = self.function_value(func, &env)?;
                env.vars.insert(func.name.node.clone());
                bindings.push((func.name.node.clone(), core, func.span));
            } else {
                let group = self.function_group_values(
                    &component
                        .iter()
                        .map(|idx| fn_decls[*idx].clone())
                        .collect::<Vec<_>>(),
                    &env,
                )?;
                for (name, value, span) in group {
                    env.vars.insert(name.clone());
                    bindings.push((name, value, span));
                }
            }
        }

        let main = self.expr(&main_decl.body, &env)?;
        let mut term = main.clone();
        for (name, value, span) in bindings.into_iter().rev() {
            term = self.record(
                Term::Let {
                    var: name,
                    expr: Box::new(value),
                    body: Box::new(term),
                },
                span.join(main_decl.span),
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
                main_decl.span,
            );
        }
        Ok(ElaboratedProgram {
            term,
            main,
            spans: self.spans.clone(),
            prelude: injected.into_iter().map(prelude_name).collect(),
        })
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
            if sig.params.is_empty() || !matches!(sig.params[0].1, Type::Nat | Type::Array) {
                return Err(ElaborateError {
                    span: func.name.span,
                    message:
                        "recursive reduced-core functions must recurse on a leading `Nat`/aggregate parameter"
                            .into(),
                });
            }
            let tag = self.recursion_tag(&func.boundedness, &sig.params[0].0)?;
            let loop_name = if sig.params.len() == 1 {
                func.name.node.clone()
            } else {
                format!("__atli_{}_loop", func.name.node)
            };
            let body_expr = if sig.params.len() == 1 {
                func.body.clone()
            } else {
                rewrite_self_calls(
                    &func.body,
                    &func.name.node,
                    &loop_name,
                    &sig.params[1..]
                        .iter()
                        .map(|(name, _, _)| name.clone())
                        .collect::<Vec<_>>(),
                )?
            };
            let mut body_env = env.clone();
            body_env.vars.insert(loop_name.clone());
            for (name, _, _) in &sig.params {
                body_env.vars.insert(name.clone());
            }
            let body = self.expr(&body_expr, &body_env)?;
            let fix = self.record(
                Term::Fix {
                    func: loop_name,
                    param: sig.params[0].0.clone(),
                    param_ty: sig.params[0].1.clone(),
                    body: Box::new(body),
                    tag,
                },
                func.span,
            );
            if sig.params.len() == 1 {
                return Ok(fix);
            }
            let mut term = self.record(
                Term::App(Box::new(fix), Box::new(Term::var(&sig.params[0].0))),
                func.span,
            );
            for (name, ty, _) in sig.params.iter().skip(1).rev() {
                term = self.record(
                    Term::Lam {
                        param: name.clone(),
                        param_ty: ty.clone(),
                        body: Box::new(term),
                    },
                    func.span,
                );
            }
            term = self.record(
                Term::Lam {
                    param: sig.params[0].0.clone(),
                    param_ty: sig.params[0].1.clone(),
                    body: Box::new(term),
                },
                func.span,
            );
            return Ok(term);
        }
        let mut body_env = env.clone();
        for (name, _, _) in &sig.params {
            body_env.vars.insert(name.clone());
        }
        let mut term = self.expr(&func.body, &body_env)?;
        for (name, ty, _) in sig.params.iter().rev() {
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

    fn function_group_values(
        &mut self,
        funcs: &[FnDecl],
        env: &Env,
    ) -> Result<Vec<(String, Term, Span)>, ElaborateError> {
        let mut recs = Vec::new();
        let group_names: BTreeSet<_> = funcs.iter().map(|func| func.name.node.clone()).collect();
        let mut base_env = env.clone();
        for name in &group_names {
            base_env.vars.insert(name.clone());
        }
        for func in funcs {
            let sig = self
                .functions
                .get(&func.name.node)
                .cloned()
                .ok_or_else(|| ElaborateError {
                    span: func.name.span,
                    message: "internal missing function signature".into(),
                })?;
            if sig.params.len() != 1 || !matches!(sig.params[0].1, Type::Nat | Type::Array) {
                return Err(ElaborateError {
                    span: func.name.span,
                    message: "recursive binding groups must contain unary `Nat`/aggregate members"
                        .into(),
                });
            }
            let tag = self.recursion_tag(&func.boundedness, &sig.params[0].0)?;
            let mut body_env = base_env.clone();
            body_env.vars.insert(sig.params[0].0.clone());
            let body = self.expr(&func.body, &body_env)?;
            recs.push(FixBinding {
                func: func.name.node.clone(),
                param: sig.params[0].0.clone(),
                param_ty: sig.params[0].1.clone(),
                body: Box::new(body),
                tag,
            });
        }
        Ok(funcs
            .iter()
            .map(|func| {
                (
                    func.name.node.clone(),
                    self.record(
                        Term::FixGroup {
                            bindings: recs.clone(),
                            entry: func.name.node.clone(),
                        },
                        func.span,
                    ),
                    func.span,
                )
            })
            .collect())
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
                if let Some(ctor) = self.aggregates.constructors.get(name).cloned() {
                    if ctor.payload_count == 0 {
                        let aggregate = Term::Mark(
                            CoverageTag::VariantAggregate,
                            Box::new(self.aggregate_array(
                                ctor.slot_count,
                                vec![Term::nat(ctor.tag)],
                                expr.span,
                            )),
                        );
                        return Ok(self.record(aggregate, expr.span));
                    }
                }
                if name != "_" && !env.vars.contains(name) && !self.functions.contains_key(name) {
                    return Err(ElaborateError {
                        span: expr.span,
                        message: format!("unbound surface variable `{name}`"),
                    });
                }
                Term::var(name)
            }
            ExprKind::Call { callee, args } => self.call(callee, args, env, expr.span)?,
            ExprKind::Prefix { op, expr: inner } => match op {
                PrefixOp::Move => Term::Move(Box::new(self.expr(inner, env)?)),
                PrefixOp::Freeze => Term::Freeze(Box::new(self.expr(inner, env)?)),
                PrefixOp::Inplace => {
                    let lowered = Term::Inplace(Box::new(self.expr(inner, env)?));
                    if matches!(inner.kind, ExprKind::RecordUpdate { .. }) {
                        Term::Mark(CoverageTag::RecordInplaceUpdate, Box::new(lowered))
                    } else {
                        lowered
                    }
                }
            },
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
            ExprKind::Scope { body } => Term::Scope(Box::new(self.expr(body, env)?)),
            ExprKind::Spawn { callee, args } => {
                if !self.functions.contains_key(&callee.node) {
                    return Err(ElaborateError {
                        span: callee.span,
                        message: format!(
                            "spawn callee `{}` is not a declared top-level function",
                            callee.node
                        ),
                    });
                }
                let call = Expr::new(
                    ExprKind::Call {
                        callee: Box::new(Expr::new(
                            ExprKind::Var(callee.node.clone()),
                            callee.span,
                        )),
                        args: args.clone(),
                    },
                    expr.span,
                );
                Term::Spawn(Box::new(self.expr(&call, env)?))
            }
            ExprKind::Await { handle } => Term::Await(Box::new(self.expr(handle, env)?)),
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
            ExprKind::RecordLit(fields) => self.record_literal(fields, env, expr.span)?,
            ExprKind::RecordUpdate {
                record,
                field,
                value,
            } => self.record_update(record, field.node.as_str(), value, env)?,
            ExprKind::Field { record, field } => {
                self.record_field(record, field.node.as_str(), env)?
            }
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
        if let ExprKind::Var(name) = &callee.kind {
            match name.as_str() {
                "mkarray" if args.len() == 2 => {
                    return Ok(Term::MkArray(
                        Box::new(self.expr(&args[0], env)?),
                        Box::new(self.expr(&args[1], env)?),
                    ));
                }
                "get" if args.len() == 2 => {
                    return Ok(Term::ArrayGet(
                        Box::new(self.expr(&args[0], env)?),
                        Box::new(self.expr(&args[1], env)?),
                    ));
                }
                "set" if args.len() == 3 => {
                    return Ok(Term::ArraySet(
                        Box::new(self.expr(&args[0], env)?),
                        Box::new(self.expr(&args[1], env)?),
                        Box::new(self.expr(&args[2], env)?),
                    ));
                }
                "len" if args.len() == 1 => {
                    return Ok(Term::ArrayLen(Box::new(self.expr(&args[0], env)?)));
                }
                "mkarray" | "get" | "set" | "len" => {
                    return Err(ElaborateError {
                        span,
                        message: format!("builtin `{name}` called with wrong arity"),
                    });
                }
                _ => {}
            }
            if let Some(ctor) = self.aggregates.constructors.get(name).cloned() {
                if args.len() != ctor.payload_count {
                    return Err(ElaborateError {
                        span,
                        message: format!(
                            "constructor `{name}` expects {} payloads",
                            ctor.payload_count
                        ),
                    });
                }
                let values = args
                    .iter()
                    .map(|arg| self.expr(arg, env))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(Term::Mark(
                    CoverageTag::VariantAggregate,
                    Box::new(self.aggregate_array(
                        ctor.slot_count,
                        std::iter::once(Term::nat(ctor.tag)).chain(values).collect(),
                        span,
                    )),
                ));
            }
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
        if arms.iter().any(|arm| {
            matches!(
                arm.pattern,
                Pattern::Constructor { .. } | Pattern::Record { .. } | Pattern::Wildcard(_)
            )
        }) && !arms
            .iter()
            .any(|arm| matches!(arm.pattern, Pattern::Zero(_)))
        {
            return self.case_aggregate(scrutinee, arms, env, span);
        }
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

    fn case_aggregate(
        &mut self,
        scrutinee: &Expr,
        arms: &[crate::surface::ast::CaseArm],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        let tmp = format!("__atli_case_{}", span.start);
        let scrut = self.expr(scrutinee, env)?;
        let body = if let Some(record_arm) = arms
            .iter()
            .find(|arm| matches!(arm.pattern, Pattern::Record { .. }))
        {
            let Pattern::Record { fields, .. } = &record_arm.pattern else {
                unreachable!()
            };
            let mut local = env.clone();
            for field in fields {
                local.vars.insert(field.node.clone());
            }
            let mut lowered = self.expr(&record_arm.body, &local)?;
            for field in fields.iter().rev() {
                let info = self
                    .aggregates
                    .fields
                    .get(&field.node)
                    .ok_or_else(|| ElaborateError {
                        span: field.span,
                        message: format!("unknown record field `{}`", field.node),
                    })?
                    .clone();
                lowered = Term::Let {
                    var: field.node.clone(),
                    expr: Box::new(Term::Mark(
                        CoverageTag::DestructureConsume,
                        Box::new(Term::ArrayGet(
                            Box::new(Term::var(&tmp)),
                            Box::new(Term::nat(u64::try_from(info.index).unwrap())),
                        )),
                    )),
                    body: Box::new(lowered),
                };
            }
            lowered
        } else {
            self.variant_case_body(&tmp, arms, env, span)?
        };
        Ok(Term::Let {
            var: tmp,
            expr: Box::new(scrut),
            body: Box::new(body),
        })
    }

    fn variant_case_body(
        &mut self,
        tmp: &str,
        arms: &[crate::surface::ast::CaseArm],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        let mut default = None;
        let mut ctor_arms = Vec::new();
        for arm in arms {
            match &arm.pattern {
                Pattern::Wildcard(_) => default = Some(&arm.body),
                Pattern::Constructor { name, args, .. } => {
                    ctor_arms.push((name.node.clone(), args.as_slice(), &arm.body, arm.span))
                }
                _ => {
                    return Err(ElaborateError {
                        span: arm.span,
                        message:
                            "aggregate case arms must be constructors, record patterns, or `_`"
                                .into(),
                    })
                }
            }
        }
        if default.is_none() {
            let missing = self.missing_constructors(&ctor_arms);
            if !missing.is_empty() {
                return Err(ElaborateError {
                    span,
                    message: format!(
                        "non-exhaustive case; missing constructors: {}",
                        missing.join(", ")
                    ),
                });
            }
        }
        let mut lowered_arms = Vec::new();
        for (ctor_name, args, body, arm_span) in ctor_arms {
            let ctor = self
                .aggregates
                .constructors
                .get(&ctor_name)
                .ok_or_else(|| ElaborateError {
                    span: arm_span,
                    message: format!("unknown constructor `{ctor_name}`"),
                })?
                .clone();
            let mut local = env.clone();
            for arg in args {
                if let Pattern::Bind(name) = arg {
                    local.vars.insert(name.node.clone());
                }
            }
            let mut branch = self.expr(body, &local)?;
            for (idx, arg) in args.iter().enumerate().rev() {
                if let Pattern::Bind(name) = arg {
                    branch = Term::Let {
                        var: name.node.clone(),
                        expr: Box::new(Term::Mark(
                            CoverageTag::ConstructorPatternDescent,
                            Box::new(Term::ArrayGet(
                                Box::new(Term::var(tmp)),
                                Box::new(Term::nat(u64::try_from(idx + 1).unwrap())),
                            )),
                        )),
                        body: Box::new(branch),
                    };
                }
            }
            lowered_arms.push((ctor.tag, branch));
        }
        let mut iter = lowered_arms.into_iter().rev();
        let mut acc = if let Some(body) = default {
            self.expr(body, env)?
        } else if let Some((_, branch)) = iter.next() {
            branch
        } else {
            Term::Unit
        };
        let tag = Term::ArrayGet(Box::new(Term::var(tmp)), Box::new(Term::nat(0)));
        for (ctor_tag, branch) in iter {
            acc = Self::tag_match_case(tag.clone(), ctor_tag, branch, acc);
        }
        Ok(acc)
    }

    fn tag_match_case(tag: Term, target: u64, yes: Term, no: Term) -> Term {
        // Variant case elaboration (`docs/calculus.md §5`): tags are unary Nats in slot 0;
        // equality to a constructor tag is encoded by repeated Nat elimination.
        if target == 0 {
            return Term::CaseNat {
                scrutinee: Box::new(tag),
                zero_body: Box::new(yes),
                succ_var: "__tag_succ".into(),
                succ_body: Box::new(no),
            };
        }
        let pred = format!("__tag_pred_{target}");
        Term::CaseNat {
            scrutinee: Box::new(tag),
            zero_body: Box::new(no.clone()),
            succ_var: pred.clone(),
            succ_body: Box::new(Self::tag_match_case(Term::var(pred), target - 1, yes, no)),
        }
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

    fn record_literal(
        &mut self,
        fields: &[(crate::surface::ast::Spanned<String>, Expr)],
        env: &Env,
        span: Span,
    ) -> Result<Term, ElaborateError> {
        let record = self
            .aggregates
            .record_for_fields(fields)
            .ok_or_else(|| ElaborateError {
                span,
                message: "record literal fields do not match a declared record type".into(),
            })?;
        let declared = self
            .aggregates
            .records
            .get(&record)
            .expect("record exists")
            .clone();
        let mut values = Vec::new();
        for (field, _) in &declared {
            let expr = fields
                .iter()
                .find(|(name, _)| name.node == *field)
                .ok_or_else(|| ElaborateError {
                    span,
                    message: format!("record literal missing field `{field}`"),
                })?;
            values.push(self.expr(&expr.1, env)?);
        }
        Ok(Term::Mark(
            CoverageTag::RecordAggregate,
            Box::new(self.aggregate_array(values.len(), values, span)),
        ))
    }

    fn record_field(
        &mut self,
        record: &Expr,
        field: &str,
        env: &Env,
    ) -> Result<Term, ElaborateError> {
        let info = self
            .aggregates
            .fields
            .get(field)
            .cloned()
            .ok_or_else(|| ElaborateError {
                span: record.span,
                message: format!("unknown record field `{field}`"),
            })?;
        Ok(Term::ArrayGet(
            Box::new(self.expr(record, env)?),
            Box::new(Term::nat(u64::try_from(info.index).unwrap())),
        ))
    }

    fn record_update(
        &mut self,
        record: &Expr,
        field: &str,
        value: &Expr,
        env: &Env,
    ) -> Result<Term, ElaborateError> {
        let info = self
            .aggregates
            .fields
            .get(field)
            .cloned()
            .ok_or_else(|| ElaborateError {
                span: record.span,
                message: format!("unknown record field `{field}`"),
            })?;
        Ok(Term::Mark(
            CoverageTag::RecordFunctionalUpdate,
            Box::new(Term::ArraySet(
                Box::new(self.expr(record, env)?),
                Box::new(Term::nat(u64::try_from(info.index).unwrap())),
                Box::new(self.expr(value, env)?),
            )),
        ))
    }

    fn aggregate_array(&mut self, slot_count: usize, values: Vec<Term>, span: Span) -> Term {
        let mut out = Term::MkArray(
            Box::new(Term::nat(u64::try_from(slot_count).unwrap())),
            Box::new(Term::nat(0)),
        );
        for (idx, value) in values.into_iter().enumerate() {
            out = self.record(
                Term::Inplace(Box::new(Term::ArraySet(
                    Box::new(out),
                    Box::new(Term::nat(u64::try_from(idx).unwrap())),
                    Box::new(value),
                ))),
                span,
            );
        }
        out
    }

    fn missing_constructors(&self, present: &[(String, &[Pattern], &Expr, Span)]) -> Vec<String> {
        let Some(first) = present.first() else {
            return Vec::new();
        };
        let Some(info) = self.aggregates.constructors.get(&first.0) else {
            return Vec::new();
        };
        let present_names = present
            .iter()
            .map(|(name, _, _, _)| name.as_str())
            .collect::<BTreeSet<_>>();
        self.aggregates
            .constructors
            .iter()
            .filter(|(_, ctor)| ctor.type_name == info.type_name)
            .filter(|(name, _)| !present_names.contains(name.as_str()))
            .map(|(name, _)| name.clone())
            .collect()
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
        TypeExpr::Array(_) => Ok(Type::Array),
        TypeExpr::Applied(name, args, _) if name == "Array" => {
            if args.len() <= 1 {
                Ok(Type::Array)
            } else {
                Err(ElaborateError {
                    span: ty.span(),
                    message: "type `Array` expects 1 type argument".into(),
                })
            }
        }
        TypeExpr::Applied(name, args, _) if name == "Task" => {
            if args.len() <= 1 {
                let inner = args
                    .first()
                    .map(lower_type)
                    .transpose()?
                    .unwrap_or(Type::Nat);
                Ok(Type::Task(Box::new(inner)))
            } else {
                Err(ElaborateError {
                    span: ty.span(),
                    message: "type `Task` expects 1 type argument".into(),
                })
            }
        }
        TypeExpr::Named(name, _) if name == "Task" => Ok(Type::Task(Box::new(Type::Nat))),
        TypeExpr::Named(_, _) | TypeExpr::Applied(_, _, _) => Ok(Type::Array),
        TypeExpr::Unique(inner, _) | TypeExpr::Preserve { inner, .. } => lower_type(inner),
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
        Pattern::Constructor { span, .. } | Pattern::Record { span, .. } => Err(ElaborateError {
            span: *span,
            message: "operation clause binders must be names or `_`".into(),
        }),
    }
}

fn desugar_pipe(lhs: Expr, rhs: Expr, span: Span) -> Result<Expr, ElaborateError> {
    match rhs.kind {
        ExprKind::Prefix { op, expr } => {
            // Pipe into prefix forms, `docs/syntax.md §5` / `docs/elaboration.md`:
            // `x |> inplace f(args)` becomes `inplace f(x, args)`; likewise freeze/move.
            let inner = desugar_pipe(lhs, *expr, span)?;
            Ok(Expr::new(
                ExprKind::Prefix {
                    op,
                    expr: Box::new(inner),
                },
                span,
            ))
        }
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
            message: "pipe RHS must be a function call, function name, or prefix form in the reduced surface"
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
        ExprKind::Scope { body } | ExprKind::Await { handle: body } => expr_mentions(body, name),
        ExprKind::Spawn { args, .. } => args.iter().any(|arg| expr_mentions(arg, name)),
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
        ExprKind::Prefix { expr, .. } => expr_mentions(expr, name),
        ExprKind::RecordLit(fields) => fields.iter().any(|(_, expr)| expr_mentions(expr, name)),
        ExprKind::RecordUpdate { record, value, .. } => {
            expr_mentions(record, name) || expr_mentions(value, name)
        }
        ExprKind::Field { record, .. } => expr_mentions(record, name),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindingMode {
    Unique,
    Preserve,
}

#[derive(Debug, Clone)]
struct UniqueBinding {
    grade: Q,
    mode: BindingMode,
    consumed_at: Option<Span>,
}

#[derive(Debug, Clone, Default)]
struct UniqueEnv {
    bindings: BTreeMap<String, UniqueBinding>,
    forgotten_bindings: BTreeMap<String, Span>,
    last_forget: Option<Span>,
}

impl UniqueEnv {
    fn bind_unique(&mut self, name: &str) {
        self.bind_mode(name, BindingMode::Unique);
    }

    fn bind_preserve(&mut self, name: &str) {
        self.bind_mode(name, BindingMode::Preserve);
    }

    fn bind_mode(&mut self, name: &str, mode: BindingMode) {
        self.bindings.insert(
            name.to_string(),
            UniqueBinding {
                grade: Q::One,
                mode,
                consumed_at: None,
            },
        );
    }

    fn bind_forgotten(&mut self, name: &str, span: Span) {
        self.forgotten_bindings.insert(name.to_string(), span);
    }

    fn consume(&mut self, name: &str, span: Span) -> Result<(), ElaborateError> {
        if let Some(binding) = self.bindings.get_mut(name) {
            debug_assert_eq!(binding.grade, Q::One);
            if binding.consumed_at.is_some() {
                return Err(ElaborateError {
                    span,
                    message: format!("cannot use `{name}`: consumed here; used again here"),
                });
            }
            binding.consumed_at = Some(span);
        }
        Ok(())
    }

    fn require_unique(
        &mut self,
        expr: &Expr,
        what: &str,
        signatures: &BTreeMap<String, (Vec<ParamMode>, ParamMode)>,
        aggregates: &AggregateEnv,
    ) -> Result<(), ElaborateError> {
        match &expr.kind {
            ExprKind::Var(name) if self.bindings.contains_key(name) => {
                if self
                    .bindings
                    .get(name)
                    .is_some_and(|binding| binding.mode == BindingMode::Preserve)
                {
                    return Err(ElaborateError {
                        span: expr.span,
                        message: format!(
                            "`{name}` is `^u`: uniqueness-preserving parameters grant threading, not mutation; take `^A` if this function must mutate."
                        ),
                    });
                }
                self.consume(name, expr.span)
            }
            ExprKind::Var(name) => {
                let extra = if self.forgotten_bindings.contains_key(name) {
                    "; uniqueness was forgotten at the helper call that bound this value"
                } else {
                    ""
                };
                Err(ElaborateError {
                    span: expr.span,
                    message: format!("{what} requires unique `{name}`, but it is shared{extra}"),
                })
            }
            ExprKind::Prefix {
                op: PrefixOp::Freeze,
                ..
            } => Err(ElaborateError {
                span: expr.span,
                message: format!("{what} requires a unique value, but `freeze` returns shared"),
            }),
            _ => {
                let unique =
                    check_unique_expr(expr, self, signatures, aggregates, &BTreeSet::new())?;
                if unique {
                    Ok(())
                } else {
                    Err(ElaborateError {
                        span: expr.span,
                        message: format!("{what} requires a unique array target"),
                    })
                }
            }
        }
    }

    fn merge_branch_consumption(&mut self, left: &Self, right: &Self) {
        for (name, binding) in &mut self.bindings {
            let l = left.bindings.get(name).and_then(|state| state.consumed_at);
            let r = right.bindings.get(name).and_then(|state| state.consumed_at);
            binding.consumed_at = binding.consumed_at.or(l).or(r);
        }
    }
}

fn check_surface_uniqueness(program: &Program) -> Result<(), ElaborateError> {
    let aggregates = AggregateEnv::from_program(program)?;
    let effectful_functions = program
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Fn(func) if func.effects.is_some() => Some(func.name.node.clone()),
            Decl::Fn(_) | Decl::Effect(_) | Decl::Type(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let signatures = program
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Fn(func) => Some((
                func.name.node.clone(),
                (
                    func.params
                        .iter()
                        .map(|param| type_mode(&param.ty))
                        .collect::<Vec<_>>(),
                    type_mode(&func.ret),
                ),
            )),
            Decl::Effect(_) | Decl::Type(_) => None,
        })
        .collect::<BTreeMap<_, _>>();
    for decl in &program.decls {
        let Decl::Fn(func) = decl else {
            continue;
        };
        let mut env = UniqueEnv::default();
        for param in &func.params {
            match type_mode(&param.ty) {
                ParamMode::Unique => env.bind_unique(&param.name.node),
                ParamMode::Preserve => env.bind_preserve(&param.name.node),
                ParamMode::Shared => {}
            }
        }
        check_unique_expr(
            &func.body,
            &mut env,
            &signatures,
            &aggregates,
            &effectful_functions,
        )?;
    }
    Ok(())
}

fn check_unique_expr(
    expr: &Expr,
    env: &mut UniqueEnv,
    signatures: &BTreeMap<String, (Vec<ParamMode>, ParamMode)>,
    aggregates: &AggregateEnv,
    effectful_functions: &BTreeSet<String>,
) -> Result<bool, ElaborateError> {
    match &expr.kind {
        ExprKind::Unit | ExprKind::Nat(_) => Ok(false),
        ExprKind::Var(name) => {
            env.consume(name, expr.span)?;
            Ok(false)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            check_unique_expr(lhs, env, signatures, aggregates, effectful_functions)?;
            check_unique_expr(rhs, env, signatures, aggregates, effectful_functions)?;
            Ok(false)
        }
        ExprKind::Pipe { lhs, rhs } => {
            let desugared = desugar_pipe((**lhs).clone(), (**rhs).clone(), expr.span)?;
            check_unique_expr(&desugared, env, signatures, aggregates, effectful_functions)
        }
        ExprKind::Scope { body } => {
            if scope_returns_task_handle(body) {
                return Err(ElaborateError {
                    span: expr.span,
                    message: "task handle may not escape scope".into(),
                });
            }
            check_unique_expr(body, env, signatures, aggregates, effectful_functions)
        }
        ExprKind::Spawn { callee, args } => {
            if effectful_functions.contains(&callee.node) {
                return Err(ElaborateError {
                    span: callee.span,
                    message: format!(
                        "spawned task must handle its own effects; `{}` has a non-empty row",
                        callee.node
                    ),
                });
            }
            if let Some((params, _)) = signatures.get(&callee.node) {
                for (arg, mode) in args.iter().zip(params) {
                    match mode {
                        ParamMode::Unique => {
                            env.require_unique(arg, "spawn argument", signatures, aggregates)?
                        }
                        ParamMode::Preserve => {
                            if let ExprKind::Var(name) = &arg.kind {
                                if env.bindings.contains_key(name) {
                                    env.consume(name, arg.span)?;
                                } else {
                                    check_unique_expr(
                                        arg,
                                        env,
                                        signatures,
                                        aggregates,
                                        effectful_functions,
                                    )?;
                                }
                            } else {
                                check_unique_expr(
                                    arg,
                                    env,
                                    signatures,
                                    aggregates,
                                    effectful_functions,
                                )?;
                            }
                        }
                        ParamMode::Shared => {
                            if check_unique_expr(
                                arg,
                                env,
                                signatures,
                                aggregates,
                                effectful_functions,
                            )? {
                                env.last_forget = Some(arg.span);
                            }
                        }
                    }
                }
                for arg in args.iter().skip(params.len()) {
                    check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
                }
            } else {
                for arg in args {
                    check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
                }
            }
            Ok(true)
        }
        ExprKind::Await { handle } => {
            check_unique_expr(handle, env, signatures, aggregates, effectful_functions)
        }
        ExprKind::QualifiedCall { args, .. } => {
            for arg in args {
                check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
            }
            Ok(false)
        }
        ExprKind::Call { callee, args } => {
            if let ExprKind::Var(name) = &callee.kind {
                return check_unique_call(
                    name,
                    args,
                    expr.span,
                    env,
                    signatures,
                    aggregates,
                    effectful_functions,
                );
            }
            check_unique_expr(callee, env, signatures, aggregates, effectful_functions)?;
            for arg in args {
                check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
            }
            Ok(false)
        }
        ExprKind::Prefix {
            op: PrefixOp::Move,
            expr: inner,
        } => {
            env.require_unique(inner, "move", signatures, aggregates)?;
            Ok(true)
        }
        ExprKind::Prefix {
            op: PrefixOp::Freeze,
            expr: inner,
        } => {
            env.require_unique(inner, "freeze", signatures, aggregates)?;
            Ok(false)
        }
        ExprKind::Prefix {
            op: PrefixOp::Inplace,
            expr: inner,
        } => {
            if let ExprKind::RecordUpdate { record, value, .. } = &inner.kind {
                env.require_unique(record, "inplace record update", signatures, aggregates)?;
                check_unique_expr(value, env, signatures, aggregates, effectful_functions)?;
                return Ok(true);
            }
            let ExprKind::Call { callee, args } = &inner.kind else {
                return Err(ElaborateError {
                    span: inner.span,
                    message: "inplace operand must be `set(array, index, value)` or record update"
                        .into(),
                });
            };
            if !matches!(&callee.kind, ExprKind::Var(name) if name == "set") || args.len() != 3 {
                return Err(ElaborateError {
                    span: inner.span,
                    message: "inplace operand must be `set(array, index, value)` or record update"
                        .into(),
                });
            }
            env.require_unique(&args[0], "inplace", signatures, aggregates)?;
            check_unique_expr(&args[1], env, signatures, aggregates, effectful_functions)?;
            check_unique_expr(&args[2], env, signatures, aggregates, effectful_functions)?;
            Ok(true)
        }
        ExprKind::Block { bindings, result } => {
            for binding in bindings {
                let unique = check_unique_expr(
                    &binding.expr,
                    env,
                    signatures,
                    aggregates,
                    effectful_functions,
                )?;
                if unique {
                    env.bind_unique(&binding.name.node);
                } else if let Some(span) = env.last_forget.take() {
                    env.bind_forgotten(&binding.name.node, span);
                }
            }
            check_unique_expr(result, env, signatures, aggregates, effectful_functions)
        }
        ExprKind::CaseNat { scrutinee, arms } => {
            let unique_scrutinee =
                matches!(&scrutinee.kind, ExprKind::Var(name) if env.bindings.contains_key(name));
            check_unique_expr(scrutinee, env, signatures, aggregates, effectful_functions)?;
            let mut branch_envs = Vec::new();
            let mut result_unique = false;
            for arm in arms {
                let mut branch = env.clone();
                if unique_scrutinee {
                    bind_unique_pattern_payloads(&arm.pattern, &mut branch, aggregates);
                }
                result_unique |= check_unique_expr(
                    &arm.body,
                    &mut branch,
                    signatures,
                    aggregates,
                    effectful_functions,
                )?;
                branch_envs.push(branch);
            }
            if branch_envs.len() == 1 {
                *env = branch_envs[0].clone();
            } else if branch_envs.len() >= 2 {
                let first = branch_envs[0].clone();
                for branch in &branch_envs[1..] {
                    env.merge_branch_consumption(&first, branch);
                }
            }
            Ok(result_unique)
        }
        ExprKind::Handle { body, clauses } => {
            check_unique_expr(body, env, signatures, aggregates, effectful_functions)?;
            for clause in clauses {
                match clause {
                    HandleClause::Return { body, .. } | HandleClause::Operation { body, .. } => {
                        check_unique_expr(body, env, signatures, aggregates, effectful_functions)?;
                    }
                }
            }
            Ok(false)
        }
        ExprKind::RecordLit(fields) => {
            for (_, field) in fields {
                check_unique_expr(field, env, signatures, aggregates, effectful_functions)?;
            }
            Ok(true)
        }
        ExprKind::RecordUpdate { record, value, .. } => {
            // Functional record update (`docs/calculus.md §5`) copies; using a unique record
            // in this shared mode consumes it by the ordinary forgetting rule (§4.2).
            check_unique_expr(record, env, signatures, aggregates, effectful_functions)?;
            check_unique_expr(value, env, signatures, aggregates, effectful_functions)?;
            Ok(true)
        }
        ExprKind::Field { record, field } => {
            if let ExprKind::Var(name) = &record.kind {
                if env.bindings.contains_key(name) {
                    if env
                        .bindings
                        .get(name)
                        .is_some_and(|binding| binding.consumed_at.is_some())
                    {
                        env.consume(name, record.span)?;
                    }
                    let info =
                        aggregates
                            .fields
                            .get(&field.node)
                            .ok_or_else(|| ElaborateError {
                                span: field.span,
                                message: format!("unknown record field `{}`", field.node),
                            })?;
                    if type_is_heap(&info.ty) {
                        return Err(ElaborateError {
                            span: field.span,
                            message: format!(
                                "field `{}` is heap-typed; freeze the record to share it, or destructure with case to take ownership",
                                field.node
                            ),
                        });
                    }
                    return Ok(false);
                }
            }
            check_unique_expr(record, env, signatures, aggregates, effectful_functions)?;
            Ok(false)
        }
    }
}

fn check_unique_call(
    name: &str,
    args: &[Expr],
    span: Span,
    env: &mut UniqueEnv,
    signatures: &BTreeMap<String, (Vec<ParamMode>, ParamMode)>,
    aggregates: &AggregateEnv,
    effectful_functions: &BTreeSet<String>,
) -> Result<bool, ElaborateError> {
    match name {
        "mkarray" => {
            if args.len() != 2 {
                return Err(ElaborateError {
                    span,
                    message: "builtin `mkarray` called with wrong arity".into(),
                });
            }
            check_unique_expr(&args[0], env, signatures, aggregates, effectful_functions)?;
            check_unique_expr(&args[1], env, signatures, aggregates, effectful_functions)?;
            Ok(true)
        }
        "get" | "len" => {
            let expected = if name == "get" { 2 } else { 1 };
            if args.len() != expected {
                return Err(ElaborateError {
                    span,
                    message: format!("builtin `{name}` called with wrong arity"),
                });
            }
            check_unique_expr(&args[0], env, signatures, aggregates, effectful_functions)?;
            for arg in &args[1..] {
                check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
            }
            Ok(false)
        }
        "set" => {
            if args.len() != 3 {
                return Err(ElaborateError {
                    span,
                    message: "builtin `set` called with wrong arity".into(),
                });
            }
            for arg in args {
                check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
            }
            Ok(true)
        }
        _ => {
            if let Some((param_modes, ret_mode)) = signatures.get(name) {
                let mut preserved_unique = false;
                for (idx, arg) in args.iter().enumerate() {
                    match param_modes.get(idx).copied().unwrap_or(ParamMode::Shared) {
                        ParamMode::Unique => {
                            env.require_unique(arg, "unique parameter", signatures, aggregates)?
                        }
                        ParamMode::Preserve => {
                            if let ExprKind::Var(var) = &arg.kind {
                                if env.bindings.contains_key(var) {
                                    preserved_unique = true;
                                    env.consume(var, arg.span)?;
                                } else {
                                    check_unique_expr(
                                        arg,
                                        env,
                                        signatures,
                                        aggregates,
                                        effectful_functions,
                                    )?;
                                }
                            } else {
                                preserved_unique |= check_unique_expr(
                                    arg,
                                    env,
                                    signatures,
                                    aggregates,
                                    effectful_functions,
                                )?;
                            }
                        }
                        ParamMode::Shared => {
                            if check_unique_expr(
                                arg,
                                env,
                                signatures,
                                aggregates,
                                effectful_functions,
                            )? {
                                env.last_forget = Some(arg.span);
                            }
                        }
                    }
                }
                Ok(match ret_mode {
                    ParamMode::Unique => true,
                    ParamMode::Preserve => preserved_unique,
                    ParamMode::Shared => false,
                })
            } else {
                for arg in args {
                    check_unique_expr(arg, env, signatures, aggregates, effectful_functions)?;
                }
                Ok(false)
            }
        }
    }
}

fn rewrite_self_calls(
    expr: &Expr,
    func: &str,
    loop_name: &str,
    captured_params: &[String],
) -> Result<Expr, ElaborateError> {
    let kind = match &expr.kind {
        ExprKind::Call { callee, args } if matches!(&callee.kind, ExprKind::Var(name) if name == func) =>
        {
            if args.len() != captured_params.len() + 1 {
                return Err(ElaborateError {
                    span: expr.span,
                    message: format!(
                        "recursive call to `{func}` must pass the recursive argument plus unchanged captured parameters"
                    ),
                });
            }
            for (arg, param) in args.iter().skip(1).zip(captured_params) {
                if !matches!(&arg.kind, ExprKind::Var(name) if name == param) {
                    return Err(ElaborateError {
                        span: arg.span,
                        message: format!(
                            "recursive call to `{func}` must pass captured parameter `{param}` unchanged"
                        ),
                    });
                }
            }
            ExprKind::Call {
                callee: Box::new(Expr::new(ExprKind::Var(loop_name.into()), callee.span)),
                args: vec![rewrite_self_calls(
                    &args[0],
                    func,
                    loop_name,
                    captured_params,
                )?],
            }
        }
        ExprKind::Call { callee, args } => ExprKind::Call {
            callee: Box::new(rewrite_self_calls(
                callee,
                func,
                loop_name,
                captured_params,
            )?),
            args: args
                .iter()
                .map(|arg| rewrite_self_calls(arg, func, loop_name, captured_params))
                .collect::<Result<Vec<_>, _>>()?,
        },
        ExprKind::QualifiedCall { effect, op, args } => ExprKind::QualifiedCall {
            effect: effect.clone(),
            op: op.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_self_calls(arg, func, loop_name, captured_params))
                .collect::<Result<Vec<_>, _>>()?,
        },
        ExprKind::Binary { op, lhs, rhs } => ExprKind::Binary {
            op: *op,
            lhs: Box::new(rewrite_self_calls(lhs, func, loop_name, captured_params)?),
            rhs: Box::new(rewrite_self_calls(rhs, func, loop_name, captured_params)?),
        },
        ExprKind::Pipe { lhs, rhs } => ExprKind::Pipe {
            lhs: Box::new(rewrite_self_calls(lhs, func, loop_name, captured_params)?),
            rhs: Box::new(rewrite_self_calls(rhs, func, loop_name, captured_params)?),
        },
        ExprKind::Block { bindings, result } => ExprKind::Block {
            bindings: bindings
                .iter()
                .map(|binding| {
                    Ok(crate::surface::ast::Binding {
                        name: binding.name.clone(),
                        expr: rewrite_self_calls(&binding.expr, func, loop_name, captured_params)?,
                        span: binding.span,
                    })
                })
                .collect::<Result<Vec<_>, ElaborateError>>()?,
            result: Box::new(rewrite_self_calls(
                result,
                func,
                loop_name,
                captured_params,
            )?),
        },
        ExprKind::CaseNat { scrutinee, arms } => ExprKind::CaseNat {
            scrutinee: Box::new(rewrite_self_calls(
                scrutinee,
                func,
                loop_name,
                captured_params,
            )?),
            arms: arms
                .iter()
                .map(|arm| {
                    Ok(crate::surface::ast::CaseArm {
                        pattern: arm.pattern.clone(),
                        body: rewrite_self_calls(&arm.body, func, loop_name, captured_params)?,
                        span: arm.span,
                    })
                })
                .collect::<Result<Vec<_>, ElaborateError>>()?,
        },
        ExprKind::RecordLit(fields) => ExprKind::RecordLit(
            fields
                .iter()
                .map(|(name, field)| {
                    Ok((
                        name.clone(),
                        rewrite_self_calls(field, func, loop_name, captured_params)?,
                    ))
                })
                .collect::<Result<Vec<_>, ElaborateError>>()?,
        ),
        ExprKind::RecordUpdate {
            record,
            field,
            value,
        } => ExprKind::RecordUpdate {
            record: Box::new(rewrite_self_calls(
                record,
                func,
                loop_name,
                captured_params,
            )?),
            field: field.clone(),
            value: Box::new(rewrite_self_calls(value, func, loop_name, captured_params)?),
        },
        ExprKind::Field { record, field } => ExprKind::Field {
            record: Box::new(rewrite_self_calls(
                record,
                func,
                loop_name,
                captured_params,
            )?),
            field: field.clone(),
        },
        ExprKind::Handle { body, clauses } => ExprKind::Handle {
            body: Box::new(rewrite_self_calls(body, func, loop_name, captured_params)?),
            clauses: clauses
                .iter()
                .map(|clause| match clause {
                    HandleClause::Return { var, body, span } => Ok(HandleClause::Return {
                        var: var.clone(),
                        body: rewrite_self_calls(body, func, loop_name, captured_params)?,
                        span: *span,
                    }),
                    HandleClause::Operation {
                        effect,
                        op,
                        param,
                        kont,
                        body,
                        span,
                    } => Ok(HandleClause::Operation {
                        effect: effect.clone(),
                        op: op.clone(),
                        param: param.clone(),
                        kont: kont.clone(),
                        body: rewrite_self_calls(body, func, loop_name, captured_params)?,
                        span: *span,
                    }),
                })
                .collect::<Result<Vec<_>, ElaborateError>>()?,
        },
        ExprKind::Scope { body } => ExprKind::Scope {
            body: Box::new(rewrite_self_calls(body, func, loop_name, captured_params)?),
        },
        ExprKind::Spawn { callee, args } => ExprKind::Spawn {
            callee: callee.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_self_calls(arg, func, loop_name, captured_params))
                .collect::<Result<Vec<_>, _>>()?,
        },
        ExprKind::Await { handle } => ExprKind::Await {
            handle: Box::new(rewrite_self_calls(
                handle,
                func,
                loop_name,
                captured_params,
            )?),
        },
        ExprKind::Prefix { op, expr: inner } => ExprKind::Prefix {
            op: *op,
            expr: Box::new(rewrite_self_calls(inner, func, loop_name, captured_params)?),
        },
        ExprKind::Unit | ExprKind::Nat(_) | ExprKind::Var(_) => expr.kind.clone(),
    };
    Ok(Expr::new(kind, expr.span))
}

fn scope_returns_task_handle(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Spawn { .. } => true,
        ExprKind::Block { bindings, result } => {
            let mut task_bindings = BTreeSet::new();
            for binding in bindings {
                if scope_returns_task_handle(&binding.expr) {
                    task_bindings.insert(binding.name.node.clone());
                }
            }
            matches!(&result.kind, ExprKind::Var(name) if task_bindings.contains(name))
                || scope_returns_task_handle(result)
        }
        ExprKind::Scope { body } => scope_returns_task_handle(body),
        ExprKind::Prefix { expr, .. } => scope_returns_task_handle(expr),
        ExprKind::Pipe { lhs, rhs } | ExprKind::Binary { lhs, rhs, .. } => {
            scope_returns_task_handle(lhs) || scope_returns_task_handle(rhs)
        }
        ExprKind::Call { callee, args } => {
            scope_returns_task_handle(callee) || args.iter().any(scope_returns_task_handle)
        }
        ExprKind::Await { .. }
        | ExprKind::Unit
        | ExprKind::Nat(_)
        | ExprKind::Var(_)
        | ExprKind::QualifiedCall { .. }
        | ExprKind::CaseNat { .. }
        | ExprKind::Handle { .. }
        | ExprKind::RecordLit(_)
        | ExprKind::RecordUpdate { .. }
        | ExprKind::Field { .. } => false,
    }
}

fn bind_unique_pattern_payloads(pattern: &Pattern, env: &mut UniqueEnv, aggregates: &AggregateEnv) {
    match pattern {
        Pattern::Record { fields, .. } => {
            for field in fields {
                if aggregates
                    .fields
                    .get(&field.node)
                    .is_some_and(|info| type_is_heap(&info.ty))
                {
                    env.bind_unique(&field.node);
                }
            }
        }
        Pattern::Constructor { name, args, .. } => {
            if let Some(ctor) = aggregates.constructors.get(&name.node) {
                for (idx, arg) in args.iter().enumerate() {
                    if ctor.payloads.get(idx).is_some_and(type_is_heap) {
                        if let Pattern::Bind(bind) = arg {
                            env.bind_unique(&bind.node);
                        }
                    }
                }
            }
        }
        Pattern::Zero(_) | Pattern::Bind(_) | Pattern::Wildcard(_) => {}
    }
}

fn type_is_heap(ty: &TypeExpr) -> bool {
    match ty {
        TypeExpr::Array(_) | TypeExpr::Named(_, _) | TypeExpr::Applied(_, _, _) => true,
        TypeExpr::Unique(inner, _) | TypeExpr::Preserve { inner, .. } => type_is_heap(inner),
        TypeExpr::Unit(_) | TypeExpr::Nat(_) | TypeExpr::Arrow(_, _, _) => false,
    }
}

fn type_mode(ty: &TypeExpr) -> ParamMode {
    match ty {
        TypeExpr::Unique(_, _) => ParamMode::Unique,
        TypeExpr::Preserve { .. } => ParamMode::Preserve,
        _ => ParamMode::Shared,
    }
}

fn declaration_scc_order(functions: &[FnDecl]) -> Vec<Vec<usize>> {
    let name_to_idx: BTreeMap<_, _> = functions
        .iter()
        .enumerate()
        .map(|(idx, func)| (func.name.node.clone(), idx))
        .collect();
    let graph: Vec<Vec<usize>> = functions
        .iter()
        .map(|func| {
            name_to_idx
                .iter()
                .filter_map(|(name, idx)| {
                    (name != &func.name.node && expr_mentions(&func.body, name)).then_some(*idx)
                })
                .collect()
        })
        .collect();
    let sccs = tarjan_sccs(&graph);
    let mut comp_of = vec![0; functions.len()];
    for (comp_idx, comp) in sccs.iter().enumerate() {
        for node in comp {
            comp_of[*node] = comp_idx;
        }
    }
    let mut comp_deps = vec![BTreeSet::new(); sccs.len()];
    for (node, deps) in graph.iter().enumerate() {
        for dep in deps {
            if comp_of[node] != comp_of[*dep] {
                comp_deps[comp_of[node]].insert(comp_of[*dep]);
            }
        }
    }
    fn visit(
        comp: usize,
        deps: &[BTreeSet<usize>],
        sccs: &[Vec<usize>],
        seen: &mut BTreeSet<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if !seen.insert(comp) {
            return;
        }
        for dep in &deps[comp] {
            visit(*dep, deps, sccs, seen, out);
        }
        out.push(sccs[comp].clone());
    }
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for comp in 0..sccs.len() {
        visit(comp, &comp_deps, &sccs, &mut seen, &mut out);
    }
    out
}

fn tarjan_sccs(graph: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct Tarjan<'a> {
        graph: &'a [Vec<usize>],
        index: usize,
        indices: Vec<Option<usize>>,
        lowlinks: Vec<usize>,
        stack: Vec<usize>,
        on_stack: BTreeSet<usize>,
        sccs: Vec<Vec<usize>>,
    }
    impl Tarjan<'_> {
        fn strongconnect(&mut self, v: usize) {
            self.indices[v] = Some(self.index);
            self.lowlinks[v] = self.index;
            self.index += 1;
            self.stack.push(v);
            self.on_stack.insert(v);

            for w in &self.graph[v] {
                if self.indices[*w].is_none() {
                    self.strongconnect(*w);
                    self.lowlinks[v] = self.lowlinks[v].min(self.lowlinks[*w]);
                } else if self.on_stack.contains(w) {
                    self.lowlinks[v] = self.lowlinks[v].min(self.indices[*w].unwrap());
                }
            }

            if self.lowlinks[v] == self.indices[v].unwrap() {
                let mut scc = Vec::new();
                loop {
                    let w = self.stack.pop().expect("tarjan stack nonempty");
                    self.on_stack.remove(&w);
                    scc.push(w);
                    if w == v {
                        break;
                    }
                }
                scc.sort_unstable();
                self.sccs.push(scc);
            }
        }
    }

    let mut tarjan = Tarjan {
        graph,
        index: 0,
        indices: vec![None; graph.len()],
        lowlinks: vec![0; graph.len()],
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        sccs: Vec::new(),
    };
    for v in 0..graph.len() {
        if tarjan.indices[v].is_none() {
            tarjan.strongconnect(v);
        }
    }
    tarjan.sccs
}
