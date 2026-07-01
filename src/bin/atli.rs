use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use atli::check::{check, CheckedWitness};
use atli::codegen::{self, CertifiedArena, EmitInput};
use atli::core::{Divergence, Term, Witness};
use atli::diagnostics::{render_source_error, render_type_error};
use atli::elaborate::{elaborate_program, ElaboratedProgram};
use atli::grade::Bound;
use atli::interp::{eval, Outcome};
use atli::surface::ast::Program;
use atli::surface::parse_program;

const STEP_BUDGET: usize = 4096;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::from(0),
        Err(CliExit::Diagnostics) => ExitCode::from(1),
        Err(CliExit::Internal(message)) => {
            eprintln!("internal error: {message}");
            ExitCode::from(2)
        }
    }
}

#[derive(Debug)]
enum CliExit {
    Diagnostics,
    Internal(String),
}

struct Pipeline {
    program: Program,
    elaborated: ElaboratedProgram,
}

fn run() -> Result<(), CliExit> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() == 2 && (args[1] == "--version" || args[1] == "version") {
        println!("atli {} ({})", env!("CARGO_PKG_VERSION"), git_sha());
        return Ok(());
    }
    if args.len() == 4 && args[1] == "run" && args[2] == "--compiled" {
        let path = &args[3];
        let src = fs::read_to_string(path).map_err(|err| CliExit::Internal(err.to_string()))?;
        return command_run_compiled(path, &src);
    }
    if args.len() == 3 && args[1] == "test" {
        return command_test(&args[2]);
    }
    if args.len() != 3 {
        eprintln!("usage: atli <check|run|core|emit|build> file.atli\n       atli run --compiled file.atli\n       atli test examples/\n       atli --version");
        return Err(CliExit::Diagnostics);
    }
    let command = &args[1];
    let path = &args[2];
    let src = fs::read_to_string(path).map_err(|err| CliExit::Internal(err.to_string()))?;
    match command.as_str() {
        "check" => command_check(path, &src),
        "run" => command_run(path, &src),
        "core" => command_core(path, &src),
        "emit" => command_emit(path, &src),
        "build" => command_build(path, &src).map(|output| {
            println!("{}", output.display());
        }),
        other => {
            eprintln!("unknown command `{other}`; expected check, run, core, emit, build, or test");
            Err(CliExit::Diagnostics)
        }
    }
}

#[derive(Debug, Default)]
struct TestDirectives {
    expect: Option<String>,
    expect_oracle: Option<String>,
    expect_compiled: Option<String>,
    expect_check_error: Option<String>,
    env: Vec<(String, String)>,
}

fn command_test(dir: &str) -> Result<(), CliExit> {
    let mut files = fs::read_dir(dir)
        .map_err(|err| CliExit::Internal(err.to_string()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("atli"))
        .collect::<Vec<_>>();
    files.sort();
    let mut failures = Vec::new();
    for path in files {
        let src = fs::read_to_string(&path).map_err(|err| CliExit::Internal(err.to_string()))?;
        let directives = parse_test_directives(&src);
        let path_s = path.display().to_string();
        if directives.expect.is_none()
            && directives.expect_oracle.is_none()
            && directives.expect_compiled.is_none()
            && directives.expect_check_error.is_none()
        {
            failures.push(format!("{path_s}: missing expect directive"));
            continue;
        }
        if let Some(needle) = directives.expect_check_error.as_deref() {
            let output = run_child(&["check", &path_s], &[])?;
            if output.status == 0 {
                failures.push(format!(
                    "{path_s}: expected check failure containing `{needle}`"
                ));
            } else if !output.combined().contains(needle) {
                failures.push(format!(
                    "{path_s}: diagnostic did not contain `{needle}`\n{}",
                    output.combined()
                ));
            } else {
                println!("ok {path_s} check-error");
            }
            continue;
        }
        let oracle_expect = directives
            .expect_oracle
            .as_ref()
            .or(directives.expect.as_ref());
        if let Some(expect) = oracle_expect {
            let output = run_child(&["run", &path_s], &[])?;
            if output.status != 0 || output.stdout.trim_end() != expect.trim_end() {
                failures.push(format!(
                    "{path_s}: oracle expected `{}`, got status {} stdout `{}` stderr `{}`",
                    expect.trim_end(),
                    output.status,
                    output.stdout.trim_end(),
                    output.stderr.trim_end()
                ));
            }
        }
        let compiled_expect = directives
            .expect_compiled
            .as_ref()
            .or(directives.expect.as_ref());
        if let Some(expect) = compiled_expect {
            let envs = directives
                .env
                .iter()
                .map(|(k, v)| (k.as_str(), v.as_str()))
                .collect::<Vec<_>>();
            let output = run_child(&["run", "--compiled", &path_s], &envs)?;
            let stdout_match = output.stdout.trim_end() == expect.trim_end();
            let combined_match = output.combined().contains(expect.trim_end());
            if output.status != 0 || !(stdout_match || combined_match) {
                failures.push(format!(
                    "{path_s}: compiled expected `{}`, got status {} stdout `{}` stderr `{}`",
                    expect.trim_end(),
                    output.status,
                    output.stdout.trim_end(),
                    output.stderr.trim_end()
                ));
            }
        }
        if failures
            .last()
            .is_none_or(|failure| !failure.starts_with(&path_s))
        {
            println!("ok {path_s}");
        }
    }
    if failures.is_empty() {
        println!("atli test: all examples passed");
        Ok(())
    } else {
        for failure in failures {
            eprintln!("FAIL {failure}");
        }
        Err(CliExit::Diagnostics)
    }
}

struct ChildOutput {
    status: i32,
    stdout: String,
    stderr: String,
}

impl ChildOutput {
    fn combined(&self) -> String {
        format!("{}{}", self.stdout, self.stderr)
    }
}

fn run_child(args: &[&str], envs: &[(&str, &str)]) -> Result<ChildOutput, CliExit> {
    let exe = env::current_exe().map_err(|err| CliExit::Internal(err.to_string()))?;
    let mut cmd = Command::new(exe);
    cmd.args(args);
    for (key, value) in envs {
        cmd.env(key, value);
    }
    let output = cmd
        .output()
        .map_err(|err| CliExit::Internal(err.to_string()))?;
    Ok(ChildOutput {
        status: output.status.code().unwrap_or(255),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

fn parse_test_directives(src: &str) -> TestDirectives {
    let mut directives = TestDirectives::default();
    for line in src.lines() {
        let Some(rest) = line.trim_start().strip_prefix("//") else {
            if line.trim().is_empty() {
                continue;
            }
            break;
        };
        let rest = rest.trim_start();
        if let Some(value) = rest.strip_prefix("expect: ") {
            directives.expect = Some(value.to_string());
        } else if let Some(value) = rest.strip_prefix("expect-oracle: ") {
            directives.expect_oracle = Some(value.to_string());
        } else if let Some(value) = rest.strip_prefix("expect-compiled: ") {
            directives.expect_compiled = Some(value.to_string());
        } else if let Some(value) = rest.strip_prefix("expect-check-error: ") {
            directives.expect_check_error = Some(value.to_string());
        } else if let Some(value) = rest.strip_prefix("env: ") {
            if let Some((key, val)) = value.split_once('=') {
                directives.env.push((key.to_string(), val.to_string()));
            }
        }
    }
    directives
}

fn git_sha() -> String {
    if let Some(sha) = option_env!("ATLI_GIT_SHA") {
        return sha.to_string();
    }
    Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .filter(|sha| !sha.is_empty())
        .unwrap_or_else(|| "unknown".to_string())
}

fn parse_elaborate(path: &str, src: &str) -> Result<Pipeline, CliExit> {
    let program = parse_program(src).map_err(|err| {
        eprint!("{}", render_source_error(path, src, &err));
        CliExit::Diagnostics
    })?;
    let elaborated = elaborate_program(&program).map_err(|err| {
        eprint!("{}", render_source_error(path, src, &err));
        CliExit::Diagnostics
    })?;
    Ok(Pipeline {
        program,
        elaborated,
    })
}

fn checked_or_diag(
    path: &str,
    src: &str,
    elaborated: &ElaboratedProgram,
) -> Result<CheckedWitness, CliExit> {
    check(&elaborated.term).map_err(|err| {
        eprint!("{}", render_type_error(path, src, &err, &elaborated.spans));
        CliExit::Diagnostics
    })
}

fn command_check(path: &str, src: &str) -> Result<(), CliExit> {
    let pipeline = parse_elaborate(path, src)?;
    let checked = checked_or_diag(path, src, &pipeline.elaborated)?;
    print_witness(checked.witness());
    Ok(())
}

fn command_run(path: &str, src: &str) -> Result<(), CliExit> {
    let pipeline = parse_elaborate(path, src)?;
    let checked = checked_or_diag(path, src, &pipeline.elaborated)?;
    let expect_div = checked.witness().divergence == Divergence::Div;
    let report = eval(pipeline.elaborated.term, STEP_BUDGET, expect_div);
    match report.outcome {
        Outcome::Value => {
            println!("{}", render_value(&report.final_term));
            Ok(())
        }
        Outcome::BudgetExhaustedDiv => {
            println!("budget exhausted after {STEP_BUDGET} steps (classified Div)");
            Ok(())
        }
        other => Err(CliExit::Internal(format!(
            "evaluation ended with {other:?}: {}",
            report.final_term
        ))),
    }
}

fn command_core(path: &str, src: &str) -> Result<(), CliExit> {
    let pipeline = parse_elaborate(path, src)?;
    println!("core:\n{}", pipeline.elaborated.term);
    println!("\nspan table:");
    for line in pipeline.elaborated.spans.debug_lines() {
        println!("  {line}");
    }
    if let Err(err) = check(&pipeline.elaborated.term) {
        println!("\ncheck diagnostic:");
        print!(
            "{}",
            render_type_error(path, src, &err, &pipeline.elaborated.spans)
        );
    }
    Ok(())
}

fn command_emit(path: &str, src: &str) -> Result<(), CliExit> {
    let pipeline = parse_elaborate(path, src)?;
    let checked = checked_or_diag(path, src, &pipeline.elaborated)?;
    let arena = CertifiedArena::from_checked(&checked).map_err(|err| {
        eprintln!("codegen error: {err}");
        CliExit::Diagnostics
    })?;
    let emission = codegen::emit(EmitInput {
        program: &pipeline.program,
        elaborated: &pipeline.elaborated,
        checked: &checked,
        arena,
    })
    .map_err(|err| {
        eprintln!("codegen error: {err}");
        CliExit::Diagnostics
    })?;
    print!("{}", emission.mlir);
    Ok(())
}

fn command_build(path: &str, src: &str) -> Result<PathBuf, CliExit> {
    let pipeline = parse_elaborate(path, src)?;
    let checked = checked_or_diag(path, src, &pipeline.elaborated)?;
    let arena = CertifiedArena::from_checked(&checked).map_err(|err| {
        eprintln!("codegen error: {err}");
        CliExit::Diagnostics
    })?;
    let output_path = build_output_path(path);
    let output = codegen::build(
        EmitInput {
            program: &pipeline.program,
            elaborated: &pipeline.elaborated,
            checked: &checked,
            arena,
        },
        Path::new(path),
        &output_path,
    )
    .map_err(|err| {
        eprintln!("codegen error: {err}");
        CliExit::Diagnostics
    })?;
    Ok(output.executable)
}

fn command_run_compiled(path: &str, src: &str) -> Result<(), CliExit> {
    let executable = command_build(path, src)?;
    let output = Command::new(&executable)
        .output()
        .map_err(|err| CliExit::Internal(err.to_string()))?;
    print!("{}", String::from_utf8_lossy(&output.stdout));
    eprint!("{}", String::from_utf8_lossy(&output.stderr));
    if output.status.success() {
        Ok(())
    } else {
        Err(CliExit::Internal(format!(
            "compiled program exited with {:?}",
            output.status.code()
        )))
    }
}

fn build_output_path(path: &str) -> PathBuf {
    let stem = Path::new(path)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("atli_program");
    PathBuf::from(".").join(stem)
}

fn print_witness(witness: &Witness) {
    println!("type: {}", witness.ty);
    println!("effects: {}", witness.effects);
    println!("β: {}", witness.bound);
    println!(
        "divergence: {}",
        match witness.divergence {
            Divergence::Terminates => "Terminates",
            Divergence::Div => "Div",
        }
    );
}

fn render_value(term: &Term) -> String {
    match nat_value(term) {
        Some(value) => value.to_string(),
        None => term.to_string(),
    }
}

fn nat_value(term: &Term) -> Option<u64> {
    match term {
        Term::Zero => Some(0),
        Term::Succ(inner) => nat_value(inner).map(|value| value + 1),
        _ => None,
    }
}

#[allow(dead_code)]
fn _format_bound(bound: Bound) -> String {
    bound.to_string()
}
