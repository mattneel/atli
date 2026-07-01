use std::env;
use std::fs;
use std::process::ExitCode;

use atli::check::check;
use atli::core::{Divergence, Term, Witness};
use atli::diagnostics::{render_source_error, render_type_error};
use atli::elaborate::{elaborate_program, ElaboratedProgram};
use atli::grade::Bound;
use atli::interp::{eval, Outcome};
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

fn run() -> Result<(), CliExit> {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        eprintln!("usage: atli <check|run|core> file.atli");
        return Err(CliExit::Diagnostics);
    }
    let command = &args[1];
    let path = &args[2];
    let src = fs::read_to_string(path).map_err(|err| CliExit::Internal(err.to_string()))?;
    match command.as_str() {
        "check" => command_check(path, &src),
        "run" => command_run(path, &src),
        "core" => command_core(path, &src),
        other => {
            eprintln!("unknown command `{other}`; expected check, run, or core");
            Err(CliExit::Diagnostics)
        }
    }
}

fn parse_elaborate(path: &str, src: &str) -> Result<ElaboratedProgram, CliExit> {
    let program = parse_program(src).map_err(|err| {
        eprint!("{}", render_source_error(path, src, &err));
        CliExit::Diagnostics
    })?;
    elaborate_program(&program).map_err(|err| {
        eprint!("{}", render_source_error(path, src, &err));
        CliExit::Diagnostics
    })
}

fn command_check(path: &str, src: &str) -> Result<(), CliExit> {
    let elaborated = parse_elaborate(path, src)?;
    match check(&elaborated.term) {
        Ok(checked) => {
            print_witness(checked.witness());
            Ok(())
        }
        Err(err) => {
            eprint!("{}", render_type_error(path, src, &err, &elaborated.spans));
            Err(CliExit::Diagnostics)
        }
    }
}

fn command_run(path: &str, src: &str) -> Result<(), CliExit> {
    let elaborated = parse_elaborate(path, src)?;
    let checked = match check(&elaborated.term) {
        Ok(checked) => checked,
        Err(err) => {
            eprint!("{}", render_type_error(path, src, &err, &elaborated.spans));
            return Err(CliExit::Diagnostics);
        }
    };
    let expect_div = checked.witness().divergence == Divergence::Div;
    let report = eval(elaborated.term, STEP_BUDGET, expect_div);
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
    let elaborated = parse_elaborate(path, src)?;
    println!("core:\n{}", elaborated.term);
    println!("\nspan table:");
    for line in elaborated.spans.debug_lines() {
        println!("  {line}");
    }
    if let Err(err) = check(&elaborated.term) {
        println!("\ncheck diagnostic:");
        print!("{}", render_type_error(path, src, &err, &elaborated.spans));
    }
    Ok(())
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
