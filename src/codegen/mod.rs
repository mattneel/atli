//! Tier-1 native lowering for finite Atli programs.
//!
//! The arena boundary implements `docs/calculus.md §9.1`: finite `β` is read only through
//! a `CertifiedGrade`, counts tier-1 i64 frame slots, and sizes the generated MLIR arena.
//! The public arena API deliberately has no raw-integer constructor.
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
use crate::surface::ast::{
    BinaryOp, Boundedness, Decl, Expr, ExprKind, FnDecl, Pattern, Program, TypeExpr,
};

const BUILD_DIR: &str = "target/atli";

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
                "Div functions require the growable backend — tier 2",
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
    pub runtime_c: String,
    pub arena_slots: u32,
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
    pub mlir_path: PathBuf,
    pub llvm_mlir_path: PathBuf,
    pub llvm_ir_path: PathBuf,
    pub runtime_path: PathBuf,
    pub emission: Emission,
}

/// Emit the load-bearing MLIR module (`docs/calculus.md §9.1`). Nothing here pre-runs the
/// program: the oracle is reserved for tests after native execution.
pub fn emit(input: EmitInput<'_>) -> Result<Emission, CodegenError> {
    ensure_fragment(input.elaborated, input.checked)?;
    let arena_slots = input.arena.slots();
    let mut module = MlirModule::new(input.program, arena_slots);
    let mlir = module.emit_module()?;
    Ok(Emission {
        mlir,
        runtime_c: runtime_shim(),
        arena_slots,
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
    let mlir_path = Path::new(BUILD_DIR).join(format!("{stem}.mlir"));
    let llvm_mlir_path = Path::new(BUILD_DIR).join(format!("{stem}.llvm.mlir"));
    let llvm_ir_path = Path::new(BUILD_DIR).join(format!("{stem}.ll"));
    let runtime_path = Path::new(BUILD_DIR).join("runtime.c");
    fs::write(&mlir_path, &emission.mlir).map_err(|err| CodegenError::new(err.to_string()))?;
    fs::write(&runtime_path, &emission.runtime_c)
        .map_err(|err| CodegenError::new(err.to_string()))?;

    run_tool(
        find_tool(
            "ATLI_MLIR_OPT",
            &["mlir-opt", "/usr/lib/llvm-22/bin/mlir-opt"],
        )
        .ok_or_else(|| CodegenError::new("no mlir-opt found; install mlir-22-tools"))?,
        &[
            mlir_path.as_os_str(),
            "--convert-scf-to-cf".as_ref(),
            "--convert-cf-to-llvm".as_ref(),
            "--convert-func-to-llvm".as_ref(),
            "--convert-arith-to-llvm".as_ref(),
            "--finalize-memref-to-llvm".as_ref(),
            "--reconcile-unrealized-casts".as_ref(),
            "-o".as_ref(),
            llvm_mlir_path.as_os_str(),
        ],
    )?;
    run_tool(
        find_tool(
            "ATLI_MLIR_TRANSLATE",
            &["mlir-translate", "/usr/lib/llvm-22/bin/mlir-translate"],
        )
        .ok_or_else(|| CodegenError::new("no mlir-translate found; install mlir-22-tools"))?,
        &[
            "--mlir-to-llvmir".as_ref(),
            llvm_mlir_path.as_os_str(),
            "-o".as_ref(),
            llvm_ir_path.as_os_str(),
        ],
    )?;
    run_tool(
        find_tool("ATLI_CLANG", &["clang-22", "clang"])
            .ok_or_else(|| CodegenError::new("no clang found; install clang-22"))?,
        &[
            llvm_ir_path.as_os_str(),
            runtime_path.as_os_str(),
            "-o".as_ref(),
            output_path.as_os_str(),
        ],
    )?;

    Ok(BuildOutput {
        executable: output_path.to_path_buf(),
        mlir_path,
        llvm_mlir_path,
        llvm_ir_path,
        runtime_path,
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
    _elaborated: &ElaboratedProgram,
    checked: &CheckedWitness,
) -> Result<(), CodegenError> {
    if checked.witness().divergence == Divergence::Div || checked.witness().bound == Bound::Omega {
        return Err(CodegenError::new(
            "Div functions require the growable backend — tier 2",
        ));
    }
    Ok(())
}

fn run_tool(program: PathBuf, args: &[&std::ffi::OsStr]) -> Result<(), CodegenError> {
    let output = Command::new(&program)
        .args(args)
        .output()
        .map_err(|err| CodegenError::new(err.to_string()))?;
    if output.status.success() {
        return Ok(());
    }
    Err(CodegenError::new(format!(
        "{} failed: {}",
        program.display(),
        String::from_utf8_lossy(&output.stderr)
    )))
}

fn find_tool(env_var: &str, names: &[&str]) -> Option<PathBuf> {
    if let Ok(path) = std::env::var(env_var) {
        let path = PathBuf::from(path);
        if path.exists() {
            return Some(path);
        }
    }
    for name in names {
        let path = PathBuf::from(name);
        if path.exists() {
            return Some(path);
        }
        if Command::new(name)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
        {
            return Some(PathBuf::from(name));
        }
    }
    None
}

fn runtime_shim() -> String {
    "#include <stdint.h>\n\
     #include <stdio.h>\n\
     #include <stdlib.h>\n\
     extern int64_t atli_program_main(void);\n\
     extern int64_t atli_high_water_value(void);\n\
     extern int64_t atli_beta_slots(void);\n\
     void atli_trap_overflow(void) {\n\
       fprintf(stderr, \"ATLI ARENA OVERFLOW: certified beta violated\\n\");\n\
       exit(86);\n\
     }\n\
     void atli_trap_one_shot(void) {\n\
       fprintf(stderr, \"ATLI ONE-SHOT VIOLATED\\n\");\n\
       exit(87);\n\
     }\n\
     int main(void) {\n\
       int64_t result = atli_program_main();\n\
       printf(\"%lld\\n\", (long long)result);\n\
       fprintf(stderr, \"ATLI_HIGH_WATER=%lld ATLI_BETA=%lld\\n\",\n\
               (long long)atli_high_water_value(), (long long)atli_beta_slots());\n\
       return 0;\n\
     }\n"
    .into()
}

struct MlirModule<'a> {
    program: &'a Program,
    arena_slots: u32,
    functions: BTreeMap<String, usize>,
}

impl<'a> MlirModule<'a> {
    fn new(program: &'a Program, arena_slots: u32) -> Self {
        let functions = program
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fn(func) => Some((func.name.node.clone(), func.params.len())),
                Decl::Effect(_) => None,
            })
            .collect();
        Self {
            program,
            arena_slots,
            functions,
        }
    }

    fn emit_module(&mut self) -> Result<String, CodegenError> {
        let mut out = String::new();
        out.push_str("// Atli tier-1 MLIR lowering. docs/calculus.md §9.1\n");
        out.push_str(&format!(
            "// arena_slots = certified_beta + C = {} + 0\n",
            self.arena_slots
        ));
        out.push_str("module attributes {");
        out.push_str(&format!(
            "atli.certified_beta_slots = {} : i64, atli.arena_overhead_slots = 0 : i64",
            self.arena_slots
        ));
        out.push_str("} {\n");
        out.push_str("  memref.global \"private\" @atli_high_water : memref<1xi64> = dense<0>\n");
        out.push_str("  func.func private @atli_trap_overflow() -> ()\n");
        out.push_str("  func.func private @atli_trap_one_shot() -> ()\n");
        self.emit_runtime_helpers(&mut out);
        for decl in &self.program.decls {
            match decl {
                Decl::Fn(func) => out.push_str(&self.emit_function(func)?),
                Decl::Effect(_) => {}
            }
        }
        out.push_str("  func.func @atli_program_main() -> i64 {\n");
        out.push_str("    %r = func.call @atli_fn_main() : () -> i64\n");
        out.push_str("    return %r : i64\n");
        out.push_str("  }\n");
        out.push_str("}\n");
        Ok(out)
    }

    fn emit_runtime_helpers(&self, out: &mut String) {
        out.push_str("  func.func @atli_beta_slots() -> i64 {\n");
        out.push_str(&format!(
            "    %beta = arith.constant {} : i64\n",
            self.arena_slots
        ));
        out.push_str("    return %beta : i64\n");
        out.push_str("  }\n");
        out.push_str("  func.func @atli_high_water_value() -> i64 {\n");
        out.push_str("    %g = memref.get_global @atli_high_water : memref<1xi64>\n");
        out.push_str("    %c0 = arith.constant 0 : index\n");
        out.push_str("    %v = memref.load %g[%c0] : memref<1xi64>\n");
        out.push_str("    return %v : i64\n");
        out.push_str("  }\n");
        out.push_str("  func.func @atli_touch_frame(%slots: i64) -> () {\n");
        out.push_str(&format!(
            "    %beta = arith.constant {} : i64\n",
            self.arena_slots
        ));
        out.push_str("    %over = arith.cmpi sgt, %slots, %beta : i64\n");
        out.push_str("    scf.if %over {\n");
        out.push_str("      func.call @atli_trap_overflow() : () -> ()\n");
        out.push_str("    }\n");
        out.push_str("    %g = memref.get_global @atli_high_water : memref<1xi64>\n");
        out.push_str("    %c0 = arith.constant 0 : index\n");
        out.push_str("    %old = memref.load %g[%c0] : memref<1xi64>\n");
        out.push_str("    %gt = arith.cmpi sgt, %slots, %old : i64\n");
        out.push_str("    scf.if %gt {\n");
        out.push_str("      memref.store %slots, %g[%c0] : memref<1xi64>\n");
        out.push_str("    }\n");
        out.push_str("    return\n");
        out.push_str("  }\n");
    }

    fn emit_function(&self, func: &FnDecl) -> Result<String, CodegenError> {
        assert_nat_type(&func.ret)?;
        let mut builder = Builder::new(&self.functions);
        let mut params = Vec::new();
        let mut env = BTreeMap::new();
        for param in &func.params {
            assert_nat_type(&param.ty)?;
            let name = c_ident(&param.name.node);
            params.push(format!("%{name}: i64"));
            env.insert(param.name.node.clone(), format!("%{name}"));
        }
        let mut out = format!(
            "  func.func {}({}) -> i64 {{\n",
            mlir_func_name(&func.name.node),
            params.join(", ")
        );
        if expr_mentions_fn(&func.body, &func.name.node)
            || !matches!(func.boundedness, Boundedness::Structural)
        {
            out.push_str("    %frame = arith.constant 1 : i64\n");
            out.push_str("    func.call @atli_touch_frame(%frame) : (i64) -> ()\n");
        }
        let value = builder.expr(&func.body, &env, 4)?;
        out.push_str(&builder.out);
        out.push_str(&format!("    return {} : i64\n", value.name));
        out.push_str("  }\n");
        Ok(out)
    }
}

#[derive(Clone)]
struct Value {
    name: String,
}

struct Builder<'a> {
    out: String,
    next: usize,
    functions: &'a BTreeMap<String, usize>,
}

impl<'a> Builder<'a> {
    fn new(functions: &'a BTreeMap<String, usize>) -> Self {
        Self {
            out: String::new(),
            next: 0,
            functions,
        }
    }

    fn expr(
        &mut self,
        expr: &Expr,
        env: &BTreeMap<String, String>,
        indent: usize,
    ) -> Result<Value, CodegenError> {
        match &expr.kind {
            ExprKind::Nat(value) => Ok(self.constant(*value, indent)),
            ExprKind::Var(name) => env
                .get(name)
                .map(|name| Value { name: name.clone() })
                .or_else(|| {
                    self.functions.contains_key(name).then(|| Value {
                        name: mlir_func_name(name),
                    })
                })
                .ok_or_else(|| CodegenError::new(format!("cannot lower variable `{name}`"))),
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.expr(lhs, env, indent)?;
                let rhs = self.expr(rhs, env, indent)?;
                self.binary(*op, &lhs, &rhs, indent)
            }
            ExprKind::Call { callee, args } => self.call(callee, args, env, indent),
            ExprKind::Pipe { lhs, rhs } => {
                let desugared = pipe_to_call((**lhs).clone(), (**rhs).clone())?;
                self.expr(&desugared, env, indent)
            }
            ExprKind::Block { bindings, result } => {
                let mut local = env.clone();
                for binding in bindings {
                    let value = self.expr(&binding.expr, &local, indent)?;
                    local.insert(binding.name.node.clone(), value.name);
                }
                self.expr(result, &local, indent)
            }
            ExprKind::CaseNat { scrutinee, arms } => self.case_nat(scrutinee, arms, env, indent),
            ExprKind::Unit => Err(CodegenError::new(
                "tier-1 native lowering currently supports Nat results only",
            )),
            ExprKind::QualifiedCall { .. } | ExprKind::Handle { .. } => Err(CodegenError::new(
                "effects and handlers are Sprint 07 territory for tier-1 native lowering",
            )),
        }
    }

    fn constant(&mut self, value: u64, indent: usize) -> Value {
        let name = self.fresh("c");
        self.line(indent, &format!("{name} = arith.constant {value} : i64"));
        Value { name }
    }

    fn binary(
        &mut self,
        op: BinaryOp,
        lhs: &Value,
        rhs: &Value,
        indent: usize,
    ) -> Result<Value, CodegenError> {
        match op {
            BinaryOp::Add => {
                let out = self.fresh("add");
                self.line(
                    indent,
                    &format!("{out} = arith.addi {}, {} : i64", lhs.name, rhs.name),
                );
                Ok(Value { name: out })
            }
            BinaryOp::Mul => {
                let out = self.fresh("mul");
                self.line(
                    indent,
                    &format!("{out} = arith.muli {}, {} : i64", lhs.name, rhs.name),
                );
                Ok(Value { name: out })
            }
            BinaryOp::Sub => self.monus(lhs, rhs, indent),
        }
    }

    fn monus(&mut self, lhs: &Value, rhs: &Value, indent: usize) -> Result<Value, CodegenError> {
        let cmp = self.fresh("gt");
        self.line(
            indent,
            &format!("{cmp} = arith.cmpi sgt, {}, {} : i64", lhs.name, rhs.name),
        );
        let out = self.fresh("monus");
        self.line(indent, &format!("{out} = scf.if {cmp} -> (i64) {{"));
        let diff = self.fresh("diff");
        self.line(
            indent + 2,
            &format!("{diff} = arith.subi {}, {} : i64", lhs.name, rhs.name),
        );
        self.line(indent + 2, &format!("scf.yield {diff} : i64"));
        self.line(indent, "} else {");
        let zero = self.fresh("zero");
        self.line(indent + 2, &format!("{zero} = arith.constant 0 : i64"));
        self.line(indent + 2, &format!("scf.yield {zero} : i64"));
        self.line(indent, "}");
        Ok(Value { name: out })
    }

    fn call(
        &mut self,
        callee: &Expr,
        args: &[Expr],
        env: &BTreeMap<String, String>,
        indent: usize,
    ) -> Result<Value, CodegenError> {
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
        let values = args
            .iter()
            .map(|arg| self.expr(arg, env, indent))
            .collect::<Result<Vec<_>, _>>()?;
        let result = self.fresh("call");
        let arg_names = values
            .iter()
            .map(|value| value.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let arg_tys = std::iter::repeat_n("i64", values.len())
            .collect::<Vec<_>>()
            .join(", ");
        self.line(
            indent,
            &format!(
                "{result} = func.call @{}({arg_names}) : ({arg_tys}) -> i64",
                c_func_name(name)
            ),
        );
        Ok(Value { name: result })
    }

    fn case_nat(
        &mut self,
        scrutinee: &Expr,
        arms: &[crate::surface::ast::CaseArm],
        env: &BTreeMap<String, String>,
        indent: usize,
    ) -> Result<Value, CodegenError> {
        if arms.len() != 2 {
            return Err(CodegenError::new(
                "tier-1 Nat case expects exactly two arms",
            ));
        }
        let scrut = self.expr(scrutinee, env, indent)?;
        let zero_const = self.constant(0, indent);
        let cond = self.fresh("is_zero");
        self.line(
            indent,
            &format!(
                "{cond} = arith.cmpi eq, {}, {} : i64",
                scrut.name, zero_const.name
            ),
        );
        let out = self.fresh("case");
        self.line(indent, &format!("{out} = scf.if {cond} -> (i64) {{"));
        let zero_body = match &arms[0].pattern {
            Pattern::Zero(_) => self.expr(&arms[0].body, env, indent + 2)?,
            _ => return Err(CodegenError::new("first case arm must be `0`")),
        };
        self.line(indent + 2, &format!("scf.yield {} : i64", zero_body.name));
        self.line(indent, "} else {");
        let pred = match &arms[1].pattern {
            Pattern::Bind(name) => name.node.clone(),
            _ => return Err(CodegenError::new("second case arm must bind predecessor")),
        };
        let one = self.constant(1, indent + 2);
        let pred_value = self.fresh("pred");
        self.line(
            indent + 2,
            &format!(
                "{pred_value} = arith.subi {}, {} : i64",
                scrut.name, one.name
            ),
        );
        let mut local = env.clone();
        local.insert(pred, pred_value);
        let succ_body = self.expr(&arms[1].body, &local, indent + 2)?;
        self.line(indent + 2, &format!("scf.yield {} : i64", succ_body.name));
        self.line(indent, "}");
        Ok(Value { name: out })
    }

    fn fresh(&mut self, prefix: &str) -> String {
        let name = format!("%{prefix}{}", self.next);
        self.next += 1;
        name
    }

    fn line(&mut self, indent: usize, line: &str) {
        self.out.push_str(&" ".repeat(indent));
        self.out.push_str(line);
        self.out.push('\n');
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

fn mlir_func_name(name: &str) -> String {
    format!("@{}", c_func_name(name))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::check;
    use crate::elaborate::elaborate_program;
    use crate::surface::parse_program;

    #[test]
    fn corrupted_beta_trips_arena_overflow_in_mlir_pipeline() {
        if find_tool("ATLI_CLANG", &["clang-22", "clang"]).is_none()
            || find_tool(
                "ATLI_MLIR_OPT",
                &["mlir-opt", "/usr/lib/llvm-22/bin/mlir-opt"],
            )
            .is_none()
            || find_tool(
                "ATLI_MLIR_TRANSLATE",
                &["mlir-translate", "/usr/lib/llvm-22/bin/mlir-translate"],
            )
            .is_none()
        {
            eprintln!("skipping codegen trap test: LLVM/MLIR toolchain not found");
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
        emission.mlir = emission.mlir.replace(
            "%beta = arith.constant 1 : i64",
            "%beta = arith.constant 0 : i64",
        );
        fs::create_dir_all(BUILD_DIR).unwrap();
        let mlir_path = Path::new(BUILD_DIR).join("corrupt_beta.mlir");
        let runtime_path = Path::new(BUILD_DIR).join("corrupt_runtime.c");
        let llvm_mlir_path = Path::new(BUILD_DIR).join("corrupt_beta.llvm.mlir");
        let llvm_ir_path = Path::new(BUILD_DIR).join("corrupt_beta.ll");
        let exe = Path::new(BUILD_DIR).join("corrupt_beta");
        fs::write(&mlir_path, emission.mlir).unwrap();
        fs::write(&runtime_path, emission.runtime_c).unwrap();
        run_tool(
            find_tool(
                "ATLI_MLIR_OPT",
                &["mlir-opt", "/usr/lib/llvm-22/bin/mlir-opt"],
            )
            .unwrap(),
            &[
                mlir_path.as_os_str(),
                "--convert-scf-to-cf".as_ref(),
                "--convert-cf-to-llvm".as_ref(),
                "--convert-func-to-llvm".as_ref(),
                "--convert-arith-to-llvm".as_ref(),
                "--finalize-memref-to-llvm".as_ref(),
                "--reconcile-unrealized-casts".as_ref(),
                "-o".as_ref(),
                llvm_mlir_path.as_os_str(),
            ],
        )
        .unwrap();
        run_tool(
            find_tool(
                "ATLI_MLIR_TRANSLATE",
                &["mlir-translate", "/usr/lib/llvm-22/bin/mlir-translate"],
            )
            .unwrap(),
            &[
                "--mlir-to-llvmir".as_ref(),
                llvm_mlir_path.as_os_str(),
                "-o".as_ref(),
                llvm_ir_path.as_os_str(),
            ],
        )
        .unwrap();
        run_tool(
            find_tool("ATLI_CLANG", &["clang-22", "clang"]).unwrap(),
            &[
                llvm_ir_path.as_os_str(),
                runtime_path.as_os_str(),
                "-o".as_ref(),
                exe.as_os_str(),
            ],
        )
        .unwrap();
        let output = Command::new(&exe).output().unwrap();
        assert_eq!(output.status.code(), Some(86));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("ATLI ARENA OVERFLOW"));
    }
}
