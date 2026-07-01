use std::fs;
use std::process::Command;
use std::sync::Mutex;

static CODEGEN_LOCK: Mutex<()> = Mutex::new(());

use atli::check::check;
use atli::core::{Handler, OpClause, Term};
use atli::elaborate::elaborate_program;
use atli::grade::Label;
use atli::interp::eval;
use atli::surface::{lex, parse_program, pretty_program, TokenKind};

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_atli")
}

fn run_cli(args: &[&str]) -> (i32, String, String) {
    let output = Command::new(bin()).args(args).output().expect("run atli");
    (
        output.status.code().unwrap_or(255),
        String::from_utf8(output.stdout).expect("stdout utf8"),
        String::from_utf8(output.stderr).expect("stderr utf8"),
    )
}

#[test]
fn lexer_tokens_include_spans_and_comments_are_ignored() {
    let tokens = lex("// hi\nfn main() -> Nat = 0\n").expect("lex");
    assert!(matches!(tokens[0].kind, TokenKind::Fn));
    assert_eq!(tokens[0].span.start, 6);
    assert!(tokens
        .iter()
        .any(|token| matches!(token.kind, TokenKind::Arrow)));
}

#[test]
fn parser_reports_reduced_surface_unsupported_constructs() {
    let err = parse_program("fn bad(x: ^Nat) -> Nat = x").expect_err("unsupported ^");
    assert!(err.message.contains("not yet in the reduced surface"));
    assert_eq!(err.span.start, 10);
}

#[test]
fn pretty_reparse_elaboration_is_stable_for_examples() {
    for path in [
        "examples/fib.atli",
        "examples/log2.atli",
        "examples/server_loop.atli",
        "examples/arith.atli",
        "examples/state_handler.atli",
        "examples/default_handler.atli",
        "examples/two_effects.atli",
        "examples/even_odd.atli",
        "examples/conditional_handler.atli",
        "examples/handler_in_recursion.atli",
        "examples/drop_across_scopes.atli",
        "examples/wedge.atli",
    ] {
        let src = fs::read_to_string(path).expect(path);
        let parsed = parse_program(&src).expect(path);
        let pretty = pretty_program(&parsed);
        let reparsed = parse_program(&pretty).expect("reparse pretty output");
        let first = elaborate_program(&parsed).expect("first elaboration");
        let second = elaborate_program(&reparsed).expect("second elaboration");
        assert_eq!(first.term.to_string(), second.term.to_string(), "{path}");
    }
}

#[test]
fn surface_handler_examples_match_hand_built_core() {
    let state_src = fs::read_to_string("examples/state_handler.atli").unwrap();
    let state = elaborate_program(&parse_program(&state_src).unwrap()).unwrap();
    let core_state = Term::Handle {
        body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(7)))),
        handler: Handler::single(
            "x".into(),
            Box::new(Term::var("x")),
            OpClause {
                op_label: Label::L,
                op_param: "p".into(),
                op_k: "k".into(),
                op_body: Box::new(Term::Resume {
                    kont: Box::new(Term::var("k")),
                    arg: Box::new(Term::var("p")),
                }),
            },
        ),
    };
    assert_eq!(
        check(&state.term).unwrap().witness(),
        check(&core_state).unwrap().witness()
    );
    assert_eq!(
        eval(state.term, 32, false).final_term,
        eval(core_state, 32, false).final_term
    );

    let default_src = fs::read_to_string("examples/default_handler.atli").unwrap();
    let default = elaborate_program(&parse_program(&default_src).unwrap()).unwrap();
    let core_default = Term::Handle {
        body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        handler: Handler::single(
            "x".into(),
            Box::new(Term::var("x")),
            OpClause {
                op_label: Label::L,
                op_param: "p".into(),
                op_k: "_k".into(),
                op_body: Box::new(Term::nat(9)),
            },
        ),
    };
    assert_eq!(
        check(&default.term).unwrap().witness(),
        check(&core_default).unwrap().witness()
    );
    assert_eq!(
        eval(default.term, 32, false).final_term,
        eval(core_default, 32, false).final_term
    );
}

#[test]
fn cli_runs_examples_and_surfaces_witnesses() {
    let cases = [
        ("examples/fib.atli", "55\n"),
        ("examples/log2.atli", "0\n"),
        ("examples/arith.atli", "14\n"),
        ("examples/state_handler.atli", "7\n"),
        ("examples/default_handler.atli", "9\n"),
        ("examples/two_effects.atli", "8\n"),
        ("examples/even_odd.atli", "1\n"),
        ("examples/conditional_handler.atli", "5\n"),
        ("examples/handler_in_recursion.atli", "0\n"),
        ("examples/drop_across_scopes.atli", "9\n"),
    ];
    for (path, expected) in cases {
        let (code, stdout, stderr) = run_cli(&["run", path]);
        assert_eq!(code, 0, "{path}: {stderr}");
        assert_eq!(stdout, expected, "{path}");
    }

    let (code, stdout, stderr) = run_cli(&["check", "examples/server_loop.atli"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("β: ω"));
    assert!(stdout.contains("divergence: Div"));

    let (code, stdout, stderr) = run_cli(&["run", "examples/server_loop.atli"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("budget exhausted"));
}

#[test]
fn cli_wedge_rejects_with_source_blame_and_core_is_inspectable() {
    let (code, _stdout, stderr) = run_cli(&["check", "examples/wedge.atli"]);
    assert_eq!(code, 1);
    assert!(stderr.contains("Handle §4.7"));
    assert!(stderr.contains("extra-mention"));
    assert!(stderr.contains("examples/wedge.atli:7:9"));
    assert!(stderr.contains("z = k"));
    assert!(stderr.contains("^"));

    let (code, stdout, stderr) = run_cli(&["core", "examples/wedge.atli"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(stdout.contains("core:"));
    assert!(stdout.contains("span table:"));
    assert!(stdout.contains("check diagnostic:"));
    assert!(stdout.contains("Handle §4.7"));
}

#[test]
fn cli_unsupported_construct_exits_one_with_clear_diagnostic() {
    let (code, _stdout, stderr) = run_cli(&["check", "examples/unsupported.atli"]);
    assert_eq!(code, 1);
    assert!(stderr.contains("uniqueness `^` is not yet in the reduced surface"));
    assert!(stderr.contains("examples/unsupported.atli:2:11"));
}

#[test]
fn arithmetic_prelude_injects_only_used_functions() {
    let default_src = fs::read_to_string("examples/default_handler.atli").unwrap();
    let default = elaborate_program(&parse_program(&default_src).unwrap()).unwrap();
    assert!(default.prelude.is_empty());
    assert!(!default.term.to_string().contains("__atli_add"));

    let arith_src = fs::read_to_string("examples/arith.atli").unwrap();
    let arith = elaborate_program(&parse_program(&arith_src).unwrap()).unwrap();
    assert_eq!(
        arith.prelude,
        vec!["__atli_pred", "__atli_add", "__atli_sub", "__atli_mul"]
    );
    let core = arith.term.to_string();
    assert!(core.contains("__atli_add"));
    assert!(core.contains("__atli_sub"));
    assert!(core.contains("__atli_mul"));
}

#[test]
fn cli_unhandled_eval_outcome_is_internal_exit_two() {
    let src = "effect L { op(x: Nat) -> Nat }\nfn main() -> Nat = L.op(0)\n";
    let path = "target/unhandled_surface_test.atli";
    fs::write(path, src).unwrap();
    let (code, _stdout, stderr) = run_cli(&["run", path]);
    assert_eq!(code, 2);
    assert!(stderr.contains("internal error"));
    assert!(stderr.contains("StuckUnhandledOperation"));
}

fn has_codegen_toolchain() -> bool {
    fn has(cmd: &str) -> bool {
        Command::new(cmd)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    }
    (has("clang-22") || has("clang"))
        && (has("mlir-opt") || std::path::Path::new("/usr/lib/llvm-22/bin/mlir-opt").exists())
        && (has("mlir-translate")
            || std::path::Path::new("/usr/lib/llvm-22/bin/mlir-translate").exists())
}

#[test]
fn codegen_emit_goldens_pin_certified_arena_literals() {
    for (path, golden) in [
        ("examples/fib.atli", "tests/goldens/codegen/fib.mlir"),
        ("examples/arith.atli", "tests/goldens/codegen/arith.mlir"),
        (
            "examples/default_handler.atli",
            "tests/goldens/codegen/default_handler.mlir",
        ),
        (
            "examples/counter.atli",
            "tests/goldens/codegen/counter.mlir",
        ),
        (
            "examples/even_odd.atli",
            "tests/goldens/codegen/even_odd.mlir",
        ),
        (
            "examples/conditional_handler.atli",
            "tests/goldens/codegen/conditional_handler.mlir",
        ),
        (
            "examples/handler_in_recursion.atli",
            "tests/goldens/codegen/handler_in_recursion.mlir",
        ),
        (
            "examples/drop_across_scopes.atli",
            "tests/goldens/codegen/drop_across_scopes.mlir",
        ),
    ] {
        let (code, stdout, stderr) = run_cli(&["emit", path]);
        assert_eq!(code, 0, "{stderr}");
        assert_eq!(stdout, fs::read_to_string(golden).unwrap(), "{path}");
        assert!(stdout.contains("atli.certified_beta_slots"));
        if path.ends_with("fib.atli") {
            assert!(stdout.contains("func.call @atli_fn_fib"));
            assert!(!stdout.contains("arith.constant 55"));
        }
        if path.ends_with("default_handler.atli") {
            assert!(stdout.contains("H-op-drop"));
        }
        if path.ends_with("counter.atli") {
            assert!(stdout.contains("H-op-resume"));
            assert!(stdout.contains("L5_mentions_iff_resume"));
            assert!(stdout.contains("atli_debug_resume_once"));
        }
        if path.ends_with("conditional_handler.atli") {
            assert!(stdout.contains("atli_scope_push"));
            assert!(stdout.contains("atli_scope_perform"));
            assert!(stdout.contains("handler-scope push"));
        }
        if path.ends_with("drop_across_scopes.atli") {
            assert!(stdout.contains("atli_scope_pop"));
            assert!(stdout.contains("H-op-drop"));
        }
    }
}

#[test]
fn growable_div_backend_bounded_run_exhausts_test_iters() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping growable backend smoke: LLVM/MLIR toolchain not found");
        return;
    }
    let (code, _stdout, stderr) = run_cli(&["build", "examples/server_loop.atli"]);
    assert_eq!(code, 0, "{stderr}");
    let output = Command::new("./server_loop")
        .env("ATLI_MAX_ITERS", "5")
        .output()
        .expect("run compiled server loop");
    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains("ATLI_MAX_ITERS exhausted after 5 iterations"),
        "{stderr}"
    );
    assert!(stderr.contains("ATLI_GROWABLE_SEGMENT=64"), "{stderr}");
}

#[test]
fn compiled_native_outputs_match_oracle_for_finite_programs() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping compiled differential: LLVM/MLIR toolchain not found");
        return;
    }
    fs::create_dir_all("target/codegen_cases").unwrap();
    let cases = [
        ("fib", fs::read_to_string("examples/fib.atli").unwrap(), "55\n"),
        ("arith", fs::read_to_string("examples/arith.atli").unwrap(), "14\n"),
        ("log2", fs::read_to_string("examples/log2.atli").unwrap(), "0\n"),
        ("state_handler", fs::read_to_string("examples/state_handler.atli").unwrap(), "7\n"),
        ("default_handler", fs::read_to_string("examples/default_handler.atli").unwrap(), "9\n"),
        ("counter", fs::read_to_string("examples/counter.atli").unwrap(), "3\n"),
        ("abort", fs::read_to_string("examples/abort.atli").unwrap(), "9\n"),
        ("two_effects", fs::read_to_string("examples/two_effects.atli").unwrap(), "8\n"),
        ("even_odd", fs::read_to_string("examples/even_odd.atli").unwrap(), "1\n"),
        ("conditional_handler", fs::read_to_string("examples/conditional_handler.atli").unwrap(), "5\n"),
        ("handler_in_recursion", fs::read_to_string("examples/handler_in_recursion.atli").unwrap(), "0\n"),
        ("drop_across_scopes", fs::read_to_string("examples/drop_across_scopes.atli").unwrap(), "9\n"),
        ("const0", "fn main() -> Nat = 0\n".into(), "0\n"),
        ("const7", "fn main() -> Nat = 7\n".into(), "7\n"),
        ("add", "fn main() -> Nat = 8 + 5\n".into(), "13\n"),
        ("sub1", "fn main() -> Nat = 8 - 5\n".into(), "3\n"),
        ("sub_monus", "fn main() -> Nat = 3 - 9\n".into(), "0\n"),
        ("mul", "fn main() -> Nat = 6 * 7\n".into(), "42\n"),
        ("prec", "fn main() -> Nat = 2 + 3 * 4\n".into(), "14\n"),
        ("block_case", "fn main() -> Nat = { n = 3; case n { 0 -> 9; p -> p + 4 } }\n".into(), "6\n"),
        ("struct", "fn dec(n: Nat) -> Nat = case n { 0 -> 0; p -> dec(p) }\nfn main() -> Nat = dec(4)\n".into(), "0\n"),
        ("measure", "fn down(n: Nat) -> Nat measure n = case n { 0 -> 0; p -> down(p) }\nfn main() -> Nat = down(5)\n".into(), "0\n"),
    ];
    for (name, src, expected) in cases {
        let path = format!("target/codegen_cases/{name}.atli");
        fs::write(&path, src).unwrap();
        let (code, oracle_stdout, oracle_stderr) = run_cli(&["run", &path]);
        assert_eq!(code, 0, "oracle {name}: {oracle_stderr}");
        assert_eq!(oracle_stdout, expected, "oracle {name}");

        let (code, compiled_stdout, compiled_stderr) = run_cli(&["run", "--compiled", &path]);
        assert_eq!(code, 0, "compiled {name}: {compiled_stderr}");
        assert_eq!(compiled_stdout, oracle_stdout, "compiled {name}");
        assert!(
            compiled_stderr.contains("ATLI_HIGH_WATER="),
            "{name}: {compiled_stderr}"
        );
        let (high_water, beta) = parse_high_water(&compiled_stderr);
        assert!(
            high_water <= beta,
            "{name}: high_water={high_water}, beta={beta}"
        );
        let _ = fs::remove_file(name);
    }
}

#[test]
fn cli_test_runner_covers_examples() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    let (code, stdout, stderr) = run_cli(&["test", "examples/"]);
    assert_eq!(code, 0, "{stderr}");
    assert!(
        stdout.contains("atli test: all examples passed"),
        "{stdout}"
    );
    assert!(
        stdout.contains("examples/wedge.atli check-error"),
        "{stdout}"
    );
}

#[test]
fn forced_dynamic_dispatch_matches_handler_fast_path() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping forced-dynamic differential: LLVM/MLIR toolchain not found");
        return;
    }
    let handler_examples = [
        "examples/state_handler.atli",
        "examples/default_handler.atli",
        "examples/counter.atli",
        "examples/abort.atli",
        "examples/two_effects.atli",
        "examples/conditional_handler.atli",
        "examples/handler_in_recursion.atli",
        "examples/drop_across_scopes.atli",
    ];
    for path in handler_examples {
        let fast = Command::new(bin())
            .args(["run", "--compiled", path])
            .output()
            .expect("fast compiled run");
        assert!(
            fast.status.success(),
            "{path}: {}",
            String::from_utf8_lossy(&fast.stderr)
        );
        let dynamic = Command::new(bin())
            .env("ATLI_FORCE_DYNAMIC_DISPATCH", "1")
            .args(["run", "--compiled", path])
            .output()
            .expect("dynamic compiled run");
        assert!(
            dynamic.status.success(),
            "{path}: {}",
            String::from_utf8_lossy(&dynamic.stderr)
        );
        assert_eq!(fast.stdout, dynamic.stdout, "{path} stdout");
        assert_eq!(
            parse_high_water(&String::from_utf8(fast.stderr).unwrap()),
            parse_high_water(&String::from_utf8(dynamic.stderr).unwrap()),
            "{path} high-water"
        );
    }

    let forced = Command::new(bin())
        .env("ATLI_FORCE_DYNAMIC_DISPATCH", "1")
        .args(["emit", "examples/counter.atli"])
        .output()
        .expect("forced emit");
    assert!(forced.status.success());
    let stdout = String::from_utf8(forced.stdout).unwrap();
    assert_eq!(
        stdout,
        fs::read_to_string("tests/goldens/codegen/counter.forced-dynamic.mlir").unwrap()
    );
    assert!(stdout.contains("forced dynamic dispatch"));
    assert!(!stdout.contains("H-op-resume, calculus.md §5"));
}

#[test]
fn structural_mutual_recursion_is_rejected_with_pair_blame() {
    let src = r#"
fn even(n: Nat) -> Nat = case n {
  0 -> 1
  p -> odd(p)
}

fn odd(n: Nat) -> Nat = case n {
  0 -> 0
  p -> even(p)
}

fn main() -> Nat = even(4)
"#;
    let path = "target/structural_even_odd_reject.atli";
    fs::write(path, src).unwrap();
    let (code, _stdout, stderr) = run_cli(&["check", path]);
    assert_eq!(code, 1, "{stderr}");
    assert!(stderr.contains("FixGroup-Structural §4.8/§7.1"), "{stderr}");
    assert!(
        stderr.contains("Structural `even` calls group member `odd`"),
        "{stderr}"
    );
    assert!(
        stderr.contains("cyclic groups require `measure` or `div`"),
        "{stderr}"
    );
}

fn parse_high_water(stderr: &str) -> (u64, u64) {
    let mut high_water = None;
    let mut beta = None;
    for part in stderr.split_whitespace() {
        if let Some(value) = part.strip_prefix("ATLI_HIGH_WATER=") {
            high_water = Some(value.parse().unwrap());
        }
        if let Some(value) = part.strip_prefix("ATLI_BETA=") {
            beta = Some(value.parse().unwrap());
        }
    }
    (high_water.unwrap(), beta.unwrap())
}
