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
    if args.len() == 4 && args[1] == "run" && args[2] == "--compiled" {
        let path = &args[3];
        let src = fs::read_to_string(path).map_err(|err| CliExit::Internal(err.to_string()))?;
        return command_run_compiled(path, &src);
    }
    if args.len() != 3 {
        eprintln!("usage: atli <check|run|core|emit|build> file.atli\n       atli run --compiled file.atli");
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
            eprintln!("unknown command `{other}`; expected check, run, core, emit, or build");
            Err(CliExit::Diagnostics)
        }
    }
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
