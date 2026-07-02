//! Surface pretty-printer for the implemented Sprint 05 subset.

use crate::surface::ast::{
    BinaryOp, Boundedness, Decl, Expr, ExprKind, HandleClause, Pattern, PrefixOp, Program, TypeExpr,
};

#[must_use]
pub fn pretty_program(program: &Program) -> String {
    let mut out = String::new();
    for decl in &program.decls {
        out.push_str(&pretty_decl(decl));
        out.push_str("\n\n");
    }
    out
}

fn pretty_decl(decl: &Decl) -> String {
    match decl {
        Decl::Effect(effect) => format!(
            "effect {} {{ {}({}: {}) -> {} }}",
            effect.name.node, effect.op.node, effect.param.name.node, effect.param.ty, effect.ret
        ),
        Decl::Fn(func) => {
            let public = if func.public { "pub " } else { "" };
            let params = func
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name.node, p.ty))
                .collect::<Vec<_>>()
                .join(", ");
            let bounded = match &func.boundedness {
                Boundedness::Structural => String::new(),
                Boundedness::Measure(expr) => format!(" measure {}", pretty_expr(expr)),
                Boundedness::Div(_) => " div".into(),
            };
            let effects = if func.effects.is_some() { " ! {L}" } else { "" };
            format!(
                "{public}fn {}({params}) -> {}{effects}{bounded} = {}",
                func.name.node,
                func.ret,
                pretty_expr(&func.body)
            )
        }
    }
}

fn pretty_expr(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Unit => "()".into(),
        ExprKind::Nat(value) => value.to_string(),
        ExprKind::Var(name) => name.clone(),
        ExprKind::Call { callee, args } => format!(
            "{}({})",
            pretty_expr(callee),
            args.iter().map(pretty_expr).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::QualifiedCall { effect, op, args } => format!(
            "{effect}.{op}({})",
            args.iter().map(pretty_expr).collect::<Vec<_>>().join(", ")
        ),
        ExprKind::Binary { op, lhs, rhs } => {
            let op = match op {
                BinaryOp::Add => "+",
                BinaryOp::Sub => "-",
                BinaryOp::Mul => "*",
            };
            format!("({} {op} {})", pretty_expr(lhs), pretty_expr(rhs))
        }
        ExprKind::Pipe { lhs, rhs } => format!("{} |> {}", pretty_expr(lhs), pretty_expr(rhs)),
        ExprKind::Block { bindings, result } => {
            let mut pieces = bindings
                .iter()
                .map(|b| format!("{} = {}", b.name.node, pretty_expr(&b.expr)))
                .collect::<Vec<_>>();
            pieces.push(pretty_expr(result));
            format!("{{ {} }}", pieces.join("; "))
        }
        ExprKind::CaseNat { scrutinee, arms } => format!(
            "case {} {{ {} }}",
            pretty_expr(scrutinee),
            arms.iter()
                .map(|arm| format!(
                    "{} -> {}",
                    pretty_pattern(&arm.pattern),
                    pretty_expr(&arm.body)
                ))
                .collect::<Vec<_>>()
                .join("; ")
        ),
        ExprKind::Handle { body, clauses } => format!(
            "handle {} {{ {} }}",
            pretty_expr(body),
            clauses
                .iter()
                .map(pretty_clause)
                .collect::<Vec<_>>()
                .join("; ")
        ),
        ExprKind::Prefix { op, expr } => {
            let op = match op {
                PrefixOp::Move => "move",
                PrefixOp::Inplace => "inplace",
                PrefixOp::Freeze => "freeze",
            };
            let inner = match expr.kind {
                ExprKind::Pipe { .. } | ExprKind::Binary { .. } => {
                    format!("({})", pretty_expr(expr))
                }
                _ => pretty_expr(expr),
            };
            format!("{op} {inner}")
        }
    }
}

fn pretty_clause(clause: &HandleClause) -> String {
    match clause {
        HandleClause::Return { var, body, .. } => {
            format!("return({}) -> {}", var.node, pretty_expr(body))
        }
        HandleClause::Operation {
            effect,
            op,
            param,
            kont,
            body,
            ..
        } => format!(
            "{}.{}({}), {} -> {}",
            effect.node,
            op.node,
            pretty_pattern(param),
            pretty_pattern(kont),
            pretty_expr(body)
        ),
    }
}

fn pretty_pattern(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Zero(_) => "0".into(),
        Pattern::Bind(name) => name.node.clone(),
        Pattern::Wildcard(_) => "_".into(),
    }
}

#[allow(dead_code)]
fn _pretty_type(ty: &TypeExpr) -> String {
    ty.to_string()
}
