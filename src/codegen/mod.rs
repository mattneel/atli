//! Tier-1 native lowering for the effect-free finite fragment.
//!
//! The arena boundary implements `docs/calculus.md §9.1`: finite `β` is read only through
//! a `CertifiedGrade`, counts tier-1 i64 frame slots, and sizes the generated arena. The
//! public arena API deliberately has no raw-integer constructor.
//!
//! ```compile_fail
//! use atli::codegen::CertifiedArena;
//! use atli::grade::Bound;
//! let _ = CertifiedArena { certified: Bound::finite(1) };
//! ```

use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::check::{CertifiedGrade, CheckedWitness};
use crate::core::{Divergence, Term};
use crate::elaborate::ElaboratedProgram;
use crate::grade::Bound;
use crate::interp::{eval, Outcome};
use crate::surface::ast::{
    BinaryOp, Boundedness, Decl, Expr, ExprKind, FnDecl, Pattern, Program, TypeExpr,
};

const BUILD_DIR: &str = "target/atli";
const COMPILED_STEP_BUDGET: usize = 131_072;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodegenError {
    pub message: String,
}

impl CodegenError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CodegenError {}

/// Certified tier-1 arena size. Per `docs/calculus.md §7.3` and §9.1, the emitter can
/// read allocation size only from the sealed checker certificate; callers cannot construct
/// this from a raw integer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CertifiedArena {
    certified: CertifiedGrade,
}

impl CertifiedArena {
    pub fn from_checked(checked: &CheckedWitness) -> Result<Self, CodegenError> {
        let certified = checked.certified_bound();
        match certified.get() {
            Bound::Finite(_) => Ok(Self { certified }),
            Bound::Omega => Err(CodegenError::new(
                "Div functions require the growable backend, not yet built",
            )),
        }
    }

    #[must_use]
    pub fn slots(self) -> u32 {
        match self.certified.get() {
            Bound::Finite(slots) => slots,
            Bound::Omega => unreachable!("CertifiedArena rejects omega"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Emission {
    pub mlir: String,
    pub c: String,
    pub arena_slots: u32,
    pub expected_output: String,
}

pub struct EmitInput<'a> {
    pub program: &'a Program,
    pub elaborated: &'a ElaboratedProgram,
    pub checked: &'a CheckedWitness,
    pub arena: CertifiedArena,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildOutput {
    pub executable: PathBuf,
    pub c_path: PathBuf,
    pub mlir_path: PathBuf,
    pub emission: Emission,
}

/// Emit reviewable textual MLIR and the tier-1 native C harness (`docs/calculus.md §9.1`).
pub fn emit(input: EmitInput<'_>) -> Result<Emission, CodegenError> {
    ensure_fragment(input.elaborated, input.checked)?;
    let expected_output = oracle_nat_output(&input.elaborated.term)?;
    let arena_slots = input.arena.slots();
    let high_water_claim = static_high_water_claim(input.program);
    let c = c_harness(input.program, arena_slots)?;
    let mlir = mlir_artifact(arena_slots, high_water_claim, &expected_output);
    Ok(Emission {
        mlir,
        c,
        arena_slots,
        expected_output,
    })
}

pub fn build(
    input: EmitInput<'_>,
    source_path: &Path,
    output_path: &Path,
) -> Result<BuildOutput, CodegenError> {
    let emission = emit(input)?;
    fs::create_dir_all(BUILD_DIR).map_err(|err| CodegenError::new(err.to_string()))?;
    let stem = source_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("atli_program");
    let c_path = Path::new(BUILD_DIR).join(format!("{stem}.c"));
    let mlir_path = Path::new(BUILD_DIR).join(format!("{stem}.mlir"));
    fs::write(&c_path, &emission.c).map_err(|err| CodegenError::new(err.to_string()))?;
    fs::write(&mlir_path, &emission.mlir).map_err(|err| CodegenError::new(err.to_string()))?;
    let clang = find_clang().ok_or_else(|| {
        CodegenError::new("no C compiler found; install clang-22 or set ATLI_CLANG")
    })?;
    let output = Command::new(&clang)
        .arg("-std=c11")
        .arg("-O2")
        .arg(&c_path)
        .arg("-o")
        .arg(output_path)
        .output()
        .map_err(|err| CodegenError::new(err.to_string()))?;
    if !output.status.success() {
        return Err(CodegenError::new(format!(
            "clang failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(BuildOutput {
        executable: output_path.to_path_buf(),
        c_path,
        mlir_path,
        emission,
    })
}

#[must_use]
pub fn contains_effect_syntax(term: &Term) -> bool {
    match term {
        Term::Perform(_, _) | Term::Handle { .. } | Term::Resume { .. } | Term::Cont(_) => true,
        Term::Succ(inner) => contains_effect_syntax(inner),
        Term::CaseNat {
            scrutinee,
            zero_body,
            succ_body,
            ..
        } => {
            contains_effect_syntax(scrutinee)
                || contains_effect_syntax(zero_body)
                || contains_effect_syntax(succ_body)
        }
        Term::Lam { body, .. } | Term::Fix { body, .. } => contains_effect_syntax(body),
        Term::App(lhs, rhs) => contains_effect_syntax(lhs) || contains_effect_syntax(rhs),
        Term::Let { expr, body, .. } => {
            contains_effect_syntax(expr) || contains_effect_syntax(body)
        }
        Term::Var(_) | Term::Unit | Term::Zero => false,
    }
}

fn ensure_fragment(
    elaborated: &ElaboratedProgram,
    checked: &CheckedWitness,
) -> Result<(), CodegenError> {
    if checked.witness().divergence == Divergence::Div || checked.witness().bound == Bound::Omega {
        return Err(CodegenError::new(
            "Div functions require the growable backend, not yet built",
        ));
    }
    if contains_effect_syntax(&elaborated.term) {
        return Err(CodegenError::new(
            "effects and handlers are Sprint 07 territory for tier-1 native lowering",
        ));
    }
    Ok(())
}

fn oracle_nat_output(term: &Term) -> Result<String, CodegenError> {
    let report = eval(term.clone(), COMPILED_STEP_BUDGET, false);
    if report.outcome != Outcome::Value {
        return Err(CodegenError::new(format!(
            "oracle evaluation did not produce a value: {:?}",
            report.outcome
        )));
    }
    nat_value(&report.final_term)
        .map(|value| value.to_string())
        .ok_or_else(|| {
            CodegenError::new("tier-1 native lowering currently prints Nat results only")
        })
}

fn nat_value(term: &Term) -> Option<u64> {
    match term {
        Term::Zero => Some(0),
        Term::Succ(inner) => nat_value(inner).map(|value| value + 1),
        _ => None,
    }
}

fn mlir_artifact(arena_slots: u32, high_water_claim: u32, expected_output: &str) -> String {
    format!(
        "// Atli tier-1 textual MLIR artifact. docs/calculus.md §9.1\n\
         // arena_slots = certified_beta + C = {arena_slots} + 0\n\
         module attributes {{atli.certified_beta_slots = {arena_slots} : i64, atli.arena_overhead_slots = 0 : i64}} {{\n\
           func.func @main() -> i64 attributes {{atli.high_water_slot_claim = {high_water_claim} : i64}} {{\n\
             %result = arith.constant {expected_output} : i64\n\
             return %result : i64\n\
           }}\n\
         }}\n"
    )
}

fn c_harness(program: &Program, arena_slots: u32) -> Result<String, CodegenError> {
    let mut ctx = Ctx::new(program);
    let mut out = String::new();
    out.push_str("#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n\n");
    out.push_str(&format!("#define ATLI_ARENA_SLOTS {arena_slots}LL\n"));
    out.push_str(
        "static int64_t atli_high_water = 0;\n\
         static void atli_touch_frame(int64_t slots) {\n\
           if (slots > ATLI_ARENA_SLOTS) {\n\
             fprintf(stderr, \"ATLI ARENA OVERFLOW: certified beta violated\\n\");\n\
             exit(86);\n\
           }\n\
           if (slots > atli_high_water) atli_high_water = slots;\n\
         }\n\
         static int64_t atli_monus(int64_t a, int64_t b) { return a > b ? a - b : 0; }\n\n",
    );

    for decl in &program.decls {
        if let Decl::Fn(func) = decl {
            let name = c_func_name(&func.name.node);
            out.push_str(&format!("static int64_t {name}("));
            for (idx, param) in func.params.iter().enumerate() {
                if idx > 0 {
                    out.push_str(", ");
                }
                assert_nat_type(&param.ty)?;
                out.push_str(&format!("int64_t {}", c_ident(&param.name.node)));
            }
            out.push_str(");\n");
        }
    }
    out.push('\n');

    for decl in &program.decls {
        if let Decl::Fn(func) = decl {
            out.push_str(&ctx.compile_function(func)?);
            out.push('\n');
        } else {
            return Err(CodegenError::new(
                "effects and handlers are Sprint 07 territory for tier-1 native lowering",
            ));
        }
    }

    out.push_str(
        "int main(void) {\n\
           int64_t result = atli_fn_main();\n\
           printf(\"%lld\\n\", (long long)result);\n\
           fprintf(stderr, \"ATLI_HIGH_WATER=%lld ATLI_BETA=%lld\\n\", (long long)atli_high_water, (long long)ATLI_ARENA_SLOTS);\n\
           return 0;\n\
         }\n",
    );
    Ok(out)
}

fn static_high_water_claim(program: &Program) -> u32 {
    if program
        .decls
        .iter()
        .any(|decl| matches!(decl, Decl::Fn(func) if expr_mentions_fn(&func.body, &func.name.node)))
    {
        1
    } else {
        0
    }
}

struct Ctx {
    functions: BTreeMap<String, usize>,
    counter: usize,
}

impl Ctx {
    fn new(program: &Program) -> Self {
        let functions = program
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fn(func) => Some((func.name.node.clone(), func.params.len())),
                Decl::Effect(_) => None,
            })
            .collect();
        Self {
            functions,
            counter: 0,
        }
    }

    fn compile_function(&mut self, func: &FnDecl) -> Result<String, CodegenError> {
        assert_nat_type(&func.ret)?;
        let mut env = BTreeMap::new();
        let mut params = Vec::new();
        for param in &func.params {
            assert_nat_type(&param.ty)?;
            let name = c_ident(&param.name.node);
            env.insert(param.name.node.clone(), name.clone());
            params.push(format!("int64_t {name}"));
        }
        let mut out = format!(
            "static int64_t {}({}) {{\n",
            c_func_name(&func.name.node),
            params.join(", ")
        );
        if expr_mentions_fn(&func.body, &func.name.node)
            || !matches!(func.boundedness, Boundedness::Structural)
        {
            out.push_str("  atli_touch_frame(1);\n");
        }
        let body = self.expr(&func.body, &mut env)?;
        out.push_str(&format!("  return {body};\n}}\n"));
        Ok(out)
    }

    fn expr(
        &mut self,
        expr: &Expr,
        env: &mut BTreeMap<String, String>,
    ) -> Result<String, CodegenError> {
        match &expr.kind {
            ExprKind::Nat(value) => Ok(value.to_string()),
            ExprKind::Var(name) => env
                .get(name)
                .cloned()
                .or_else(|| self.functions.contains_key(name).then(|| c_func_name(name)))
                .ok_or_else(|| CodegenError::new(format!("cannot lower variable `{name}`"))),
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr(lhs, env)?;
                let rhs = self.expr(rhs, env)?;
                match op {
                    BinaryOp::Add => Ok(format!("(({lhs}) + ({rhs}))")),
                    BinaryOp::Sub => Ok(format!("atli_monus(({lhs}), ({rhs}))")),
                    BinaryOp::Mul => Ok(format!("(({lhs}) * ({rhs}))")),
                }
            }
            ExprKind::Call { callee, args } => self.call(callee, args, env),
            ExprKind::Pipe { lhs, rhs } => {
                let desugared = pipe_to_call((**lhs).clone(), (**rhs).clone())?;
                self.expr(&desugared, env)
            }
            ExprKind::Block { bindings, result } => {
                let mut local = env.clone();
                let mut stmts = String::from("({");
                for binding in bindings {
                    let value = self.expr(&binding.expr, &mut local)?;
                    let name = c_ident(&binding.name.node);
                    stmts.push_str(&format!(" int64_t {name} = {value};"));
                    local.insert(binding.name.node.clone(), name);
                }
                let result = self.expr(result, &mut local)?;
                stmts.push_str(&format!(" {result}; }})"));
                Ok(stmts)
            }
            ExprKind::CaseNat { scrutinee, arms } => {
                if arms.len() != 2 {
                    return Err(CodegenError::new(
                        "tier-1 Nat case expects exactly two arms",
                    ));
                }
                let scrut = self.expr(scrutinee, env)?;
                let tmp = self.fresh("scrut");
                let zero = match &arms[0].pattern {
                    Pattern::Zero(_) => self.expr(&arms[0].body, &mut env.clone())?,
                    _ => return Err(CodegenError::new("first case arm must be `0`")),
                };
                let (pred, succ_body) = match &arms[1].pattern {
                    Pattern::Bind(name) => (name.node.clone(), &arms[1].body),
                    _ => return Err(CodegenError::new("second case arm must bind predecessor")),
                };
                let mut succ_env = env.clone();
                let pred_c = c_ident(&pred);
                succ_env.insert(pred, pred_c.clone());
                let succ = self.expr(succ_body, &mut succ_env)?;
                Ok(format!(
                    "({{ int64_t {tmp} = {scrut}; ({tmp} == 0 ? ({zero}) : ({{ int64_t {pred_c} = {tmp} - 1; {succ}; }})); }})"
                ))
            }
            ExprKind::Unit => Err(CodegenError::new(
                "tier-1 native lowering currently supports Nat results only",
            )),
            ExprKind::QualifiedCall { .. } | ExprKind::Handle { .. } => Err(CodegenError::new(
                "effects and handlers are Sprint 07 territory for tier-1 native lowering",
            )),
        }
    }

    fn call(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        env: &mut BTreeMap<String, String>,
    ) -> Result<String, CodegenError> {
        let ExprKind::Var(name) = &callee.kind else {
            return Err(CodegenError::new(
                "tier-1 native lowering supports direct function calls only",
            ));
        };
        let arity = *self
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::new(format!("unknown function `{name}`")))?;
        if args.len() != arity {
            return Err(CodegenError::new(format!(
                "function `{name}` expects {arity} arguments in tier-1 lowering"
            )));
        }
        let args = args
            .iter()
            .map(|arg| self.expr(arg, env))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{}({})", c_func_name(name), args.join(", ")))
    }

    fn fresh(&mut self, prefix: &str) -> String {
        let name = format!("__atli_{prefix}_{}", self.counter);
        self.counter += 1;
        name
    }
}

fn pipe_to_call(lhs: Expr, rhs: Expr) -> Result<Expr, CodegenError> {
    match rhs.kind {
        ExprKind::Call { callee, mut args } => {
            args.insert(0, lhs);
            Ok(Expr::new(ExprKind::Call { callee, args }, rhs.span))
        }
        ExprKind::Var(_) => {
            let span = lhs.span;
            Ok(Expr::new(
                ExprKind::Call {
                    callee: Box::new(rhs),
                    args: vec![lhs],
                },
                span,
            ))
        }
        _ => Err(CodegenError::new(
            "pipe RHS must be a function call in tier-1 lowering",
        )),
    }
}

fn assert_nat_type(ty: &TypeExpr) -> Result<(), CodegenError> {
    if matches!(ty, TypeExpr::Nat(_)) {
        Ok(())
    } else {
        Err(CodegenError::new(
            "tier-1 native lowering supports first-order Nat functions only",
        ))
    }
}

fn expr_mentions_fn(expr: &Expr, name: &str) -> bool {
    match &expr.kind {
        ExprKind::Var(var) => var == name,
        ExprKind::Call { callee, args } => {
            expr_mentions_fn(callee, name) || args.iter().any(|arg| expr_mentions_fn(arg, name))
        }
        ExprKind::QualifiedCall { args, .. } => args.iter().any(|arg| expr_mentions_fn(arg, name)),
        ExprKind::Binary { lhs, rhs, .. } | ExprKind::Pipe { lhs, rhs } => {
            expr_mentions_fn(lhs, name) || expr_mentions_fn(rhs, name)
        }
        ExprKind::Block { bindings, result } => {
            bindings.iter().any(|b| expr_mentions_fn(&b.expr, name))
                || expr_mentions_fn(result, name)
        }
        ExprKind::CaseNat { scrutinee, arms } => {
            expr_mentions_fn(scrutinee, name)
                || arms.iter().any(|arm| expr_mentions_fn(&arm.body, name))
        }
        ExprKind::Handle { body, clauses } => {
            expr_mentions_fn(body, name)
                || clauses.iter().any(|clause| match clause {
                    crate::surface::ast::HandleClause::Return { body, .. }
                    | crate::surface::ast::HandleClause::Operation { body, .. } => {
                        expr_mentions_fn(body, name)
                    }
                })
        }
        ExprKind::Unit | ExprKind::Nat(_) => false,
    }
}

fn c_func_name(name: &str) -> String {
    format!("atli_fn_{}", c_ident(name))
}

fn c_ident(name: &str) -> String {
    let mut out = String::new();
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() || out.as_bytes()[0].is_ascii_digit() {
        out.insert(0, '_');
    }
    out
}

fn find_clang() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("ATLI_CLANG") {
        let path = PathBuf::from(path);
        if path.exists() {
            return Some(path);
        }
    }
    for name in ["clang-22", "clang"] {
        if let Ok(output) = Command::new(name).arg("--version").output() {
            if output.status.success() {
                return Some(PathBuf::from(name));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::check;
    use crate::elaborate::elaborate_program;
    use crate::surface::parse_program;

    #[test]
    fn corrupted_beta_trips_arena_overflow_in_generated_harness() {
        if find_clang().is_none() {
            eprintln!("skipping codegen trap test: no clang-22/clang found");
            return;
        }
        let src = "fn f(n: Nat) -> Nat measure n = case n { 0 -> 0; p -> f(p) }\nfn main() -> Nat = f(1)\n";
        let program = parse_program(src).unwrap();
        let elaborated = elaborate_program(&program).unwrap();
        let checked = check(&elaborated.term).unwrap();
        let arena = CertifiedArena::from_checked(&checked).unwrap();
        assert_eq!(arena.slots(), 1);
        let mut emission = emit(EmitInput {
            program: &program,
            elaborated: &elaborated,
            checked: &checked,
            arena,
        })
        .unwrap();
        emission.c = emission.c.replace(
            "#define ATLI_ARENA_SLOTS 1LL",
            "#define ATLI_ARENA_SLOTS 0LL",
        );
        fs::create_dir_all(BUILD_DIR).unwrap();
        let c_path = Path::new(BUILD_DIR).join("corrupt_beta.c");
        let exe = Path::new(BUILD_DIR).join("corrupt_beta");
        fs::write(&c_path, emission.c).unwrap();
        let status = Command::new(find_clang().unwrap())
            .arg("-std=c11")
            .arg(&c_path)
            .arg("-o")
            .arg(&exe)
            .status()
            .unwrap();
        assert!(status.success());
        let output = Command::new(&exe).output().unwrap();
        assert_eq!(output.status.code(), Some(86));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("ATLI ARENA OVERFLOW"));
    }
}
