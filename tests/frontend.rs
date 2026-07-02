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
    let err =
        parse_program("fn main() -> Nat = if 1 { 1 } else { 0 }").expect_err("unsupported if");
    assert!(err.message.contains("not yet in the reduced surface"));
    assert_eq!(err.span.start, 19);
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
        "examples/render.atli",
        "examples/copy_vs_inplace.atli",
        "examples/copy_functional.atli",
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
        ("examples/render.atli", "42\n"),
        ("examples/copy_vs_inplace.atli", "2\n"),
        ("examples/copy_functional.atli", "2\n"),
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
    assert!(stderr.contains("if is not yet in the reduced surface"));
    assert!(stderr.contains("examples/unsupported.atli:2:20"));
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
        ("examples/render.atli", "tests/goldens/codegen/render.mlir"),
        (
            "examples/copy_vs_inplace.atli",
            "tests/goldens/codegen/copy_vs_inplace.mlir",
        ),
        (
            "examples/copy_functional.atli",
            "tests/goldens/codegen/copy_functional.mlir",
        ),
        (
            "examples/shape_area.atli",
            "tests/goldens/codegen/shape_area.mlir",
        ),
        (
            "examples/natlist.atli",
            "tests/goldens/codegen/natlist.mlir",
        ),
        (
            "examples/mailbox.atli",
            "tests/goldens/codegen/mailbox.mlir",
        ),
        (
            "examples/record_update_inplace.atli",
            "tests/goldens/codegen/record_update_inplace.mlir",
        ),
        (
            "examples/record_update_functional.atli",
            "tests/goldens/codegen/record_update_functional.mlir",
        ),
        ("examples/fanout.atli", "tests/goldens/codegen/fanout.mlir"),
        (
            "examples/courier.atli",
            "tests/goldens/codegen/courier.mlir",
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
        ("render", fs::read_to_string("examples/render.atli").unwrap(), "42\n"),
        ("copy_vs_inplace", fs::read_to_string("examples/copy_vs_inplace.atli").unwrap(), "2\n"),
        ("copy_functional", fs::read_to_string("examples/copy_functional.atli").unwrap(), "2\n"),
        ("fanout", fs::read_to_string("examples/fanout.atli").unwrap(), "9\n"),
        ("courier", fs::read_to_string("examples/courier.atli").unwrap(), "42\n"),
        ("nursery", fs::read_to_string("examples/nursery.atli").unwrap(), "6\n"),
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
fn task_examples_report_spawn_counts_and_are_deterministic() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping task runtime smoke: LLVM/MLIR toolchain not found");
        return;
    }

    let mut outputs = std::collections::BTreeSet::new();
    for _ in 0..10 {
        let out = Command::new(bin())
            .args(["run", "--compiled", "examples/fanout.atli"])
            .output()
            .expect("compiled fanout");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        outputs.insert(String::from_utf8(out.stdout).unwrap());
        let stderr = String::from_utf8(out.stderr).unwrap();
        assert_eq!(parse_tasks_spawned(&stderr), 3, "{stderr}");
        assert!(
            parse_task_tids(&stderr).len() >= 2,
            "fanout must witness real parallel runtime thread ids: {stderr}"
        );
    }
    assert_eq!(outputs.len(), 1, "fanout must be schedule-independent");
    assert_eq!(outputs.iter().next().unwrap(), "9\n");

    let courier = Command::new(bin())
        .args(["run", "--compiled", "examples/courier.atli"])
        .output()
        .expect("compiled courier");
    assert!(
        courier.status.success(),
        "{}",
        String::from_utf8_lossy(&courier.stderr)
    );
    assert_eq!(String::from_utf8(courier.stdout).unwrap(), "42\n");
    let stderr = String::from_utf8(courier.stderr).unwrap();
    assert_eq!(parse_tasks_spawned(&stderr), 1, "{stderr}");
    assert!(parse_data_allocs(&stderr) >= 1, "{stderr}");
}

#[test]
fn compiled_array_allocations_and_bounds_are_observable() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping array allocation smoke: LLVM/MLIR toolchain not found");
        return;
    }

    let render = Command::new(bin())
        .args(["run", "--compiled", "examples/render.atli"])
        .output()
        .expect("compiled render");
    assert!(
        render.status.success(),
        "{}",
        String::from_utf8_lossy(&render.stderr)
    );
    assert_eq!(String::from_utf8(render.stdout).unwrap(), "42\n");
    assert_eq!(
        parse_data_allocs(&String::from_utf8(render.stderr).unwrap()),
        1
    );

    let inplace = Command::new(bin())
        .args(["run", "--compiled", "examples/copy_vs_inplace.atli"])
        .output()
        .expect("compiled inplace");
    assert!(
        inplace.status.success(),
        "{}",
        String::from_utf8_lossy(&inplace.stderr)
    );
    let functional = Command::new(bin())
        .args(["run", "--compiled", "examples/copy_functional.atli"])
        .output()
        .expect("compiled functional");
    assert!(
        functional.status.success(),
        "{}",
        String::from_utf8_lossy(&functional.stderr)
    );
    let inplace_allocs = parse_data_allocs(&String::from_utf8(inplace.stderr).unwrap());
    let functional_allocs = parse_data_allocs(&String::from_utf8(functional.stderr).unwrap());
    assert!(
        inplace_allocs < functional_allocs,
        "inplace={inplace_allocs}, functional={functional_allocs}"
    );

    let bounds = "fn main() -> Nat = get(mkarray(1, 0), 2)\n";
    let path = "target/bounds_surface_test.atli";
    fs::write(path, bounds).unwrap();
    let parsed = parse_program(bounds).unwrap();
    let elaborated = elaborate_program(&parsed).unwrap();
    assert_eq!(
        eval(elaborated.term, 32, false).outcome,
        atli::interp::Outcome::BoundsTrap
    );
    let (code, _stdout, stderr) = run_cli(&["build", path]);
    assert_eq!(code, 0, "{stderr}");
    let output = Command::new("./bounds_surface_test")
        .output()
        .expect("run bounds binary");
    assert_eq!(output.status.code(), Some(88));
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("ATLI BOUNDS"));
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
fn bypassed_unique_to_two_spawns_race_is_falsifiable() {
    let _guard = CODEGEN_LOCK.lock().unwrap();
    if !has_codegen_toolchain() {
        eprintln!("skipping task race falsifier: LLVM/MLIR toolchain not found");
        return;
    }
    fs::create_dir_all("target/codegen_cases").unwrap();
    let src = r#"
fn touch_one(a: ^Array) -> Nat = {
  done = inplace set(a, 0, 1)
  0
}

fn touch_two(a: ^Array) -> Nat = {
  done = inplace set(a, 0, 2)
  0
}

fn main() -> Nat = 0
"#;
    let source_path = "target/codegen_cases/unique_to_two_spawns_twin.atli";
    fs::write(source_path, src).unwrap();
    let (code, _stdout, stderr) = run_cli(&["build", source_path]);
    assert_eq!(code, 0, "{stderr}");

    let mlir = r#"// checker-bypass twin of examples/unique_to_two_spawns.atli; linked against the actual Atli shim
module attributes {atli.certified_beta_slots = 0 : i64, atli.arena_overhead_slots = 0 : i64, atli.growable = false} {
  llvm.func @atli_entry_touch_one(i64) -> i64
  llvm.func @atli_entry_touch_two(i64) -> i64
  func.func private @atli_spawn(%fn: !llvm.ptr, %arg: i64, %beta: i64, %growable: i64) -> i64
  func.func private @atli_await(%handle: i64) -> i64
  func.func private @atli_scope_enter() -> ()
  func.func private @atli_scope_exit() -> ()
  func.func private @atli_array_new(%len: i64, %fill: i64) -> i64
  func.func private @atli_array_get(%handle: i64, %idx: i64) -> i64
  func.func private @atli_array_inplace_set(%handle: i64, %idx: i64, %value: i64) -> i64
  func.func private @atli_race_perturb(%salt: i64) -> ()
  func.func @atli_beta_slots() -> i64 {
    %c0 = arith.constant 0 : i64
    return %c0 : i64
  }
  func.func @atli_fn_touch_one(%a: i64) -> i64 {
    %salt = arith.constant 1 : i64
    func.call @atli_race_perturb(%salt) : (i64) -> ()
    %idx = arith.constant 0 : i64
    %one = arith.constant 1 : i64
    %_mut = func.call @atli_array_inplace_set(%a, %idx, %one) : (i64, i64, i64) -> i64
    %z = arith.constant 0 : i64
    return %z : i64
  }
  func.func @atli_fn_touch_two(%a: i64) -> i64 {
    %salt = arith.constant 2 : i64
    func.call @atli_race_perturb(%salt) : (i64) -> ()
    %idx = arith.constant 0 : i64
    %two = arith.constant 2 : i64
    %_mut = func.call @atli_array_inplace_set(%a, %idx, %two) : (i64, i64, i64) -> i64
    %z = arith.constant 0 : i64
    return %z : i64
  }
  func.func @atli_program_main() -> i64 {
    func.call @atli_scope_enter() : () -> ()
    %len = arith.constant 1 : i64
    %fill = arith.constant 0 : i64
    %a = func.call @atli_array_new(%len, %fill) : (i64, i64) -> i64
    %beta = arith.constant 0 : i64
    %grow = arith.constant 0 : i64
    %f1 = llvm.mlir.addressof @atli_entry_touch_one : !llvm.ptr
    %h1 = func.call @atli_spawn(%f1, %a, %beta, %grow) : (!llvm.ptr, i64, i64, i64) -> i64
    %f2 = llvm.mlir.addressof @atli_entry_touch_two : !llvm.ptr
    %h2 = func.call @atli_spawn(%f2, %a, %beta, %grow) : (!llvm.ptr, i64, i64, i64) -> i64
    %_a1 = func.call @atli_await(%h1) : (i64) -> i64
    %_a2 = func.call @atli_await(%h2) : (i64) -> i64
    func.call @atli_scope_exit() : () -> ()
    %idx = arith.constant 0 : i64
    %read = func.call @atli_array_get(%a, %idx) : (i64, i64) -> i64
    return %read : i64
  }
}
"#;
    let mlir_path = "target/codegen_cases/unique_to_two_spawns_bypass.mlir";
    let llvm_mlir_path = "target/codegen_cases/unique_to_two_spawns_bypass.llvm.mlir";
    let llvm_ir_path = "target/codegen_cases/unique_to_two_spawns_bypass.ll";
    let exe = "target/codegen_cases/unique_to_two_spawns_bypass";
    fs::write(mlir_path, mlir).unwrap();
    compile_mlir_with_runtime(
        mlir_path,
        llvm_mlir_path,
        llvm_ir_path,
        "target/atli/runtime.c",
        exe,
    );

    let oracle = "0\n";
    let mut outputs = std::collections::BTreeSet::new();
    for _ in 0..40 {
        let out = Command::new(exe)
            .output()
            .expect("run pipeline race falsifier");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let stdout = String::from_utf8(out.stdout).unwrap();
        assert_ne!(
            stdout, oracle,
            "bypassed native race must diverge from copy oracle"
        );
        outputs.insert(stdout);
    }
    assert!(
        outputs.len() >= 2,
        "bypassed native race should be nondeterministic across real Atli runtime runs: {outputs:?}"
    );
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

fn tool_path(env_var: &str, names: &[&str]) -> String {
    if let Ok(path) = std::env::var(env_var) {
        return path;
    }
    for name in names {
        if Command::new(name)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
            || std::path::Path::new(name).exists()
        {
            return (*name).to_string();
        }
    }
    panic!("missing tool {env_var}");
}

fn compile_mlir_with_runtime(
    mlir: &str,
    llvm_mlir: &str,
    llvm_ir: &str,
    runtime_c: &str,
    exe: &str,
) {
    let mlir_opt = tool_path(
        "ATLI_MLIR_OPT",
        &["mlir-opt", "/usr/lib/llvm-22/bin/mlir-opt"],
    );
    let mlir_translate = tool_path(
        "ATLI_MLIR_TRANSLATE",
        &["mlir-translate", "/usr/lib/llvm-22/bin/mlir-translate"],
    );
    let clang = tool_path("ATLI_CLANG", &["clang-22", "clang"]);
    let status = Command::new(&mlir_opt)
        .args([
            mlir,
            "--convert-scf-to-cf",
            "--convert-cf-to-llvm",
            "--convert-func-to-llvm",
            "--convert-arith-to-llvm",
            "--finalize-memref-to-llvm",
            "--reconcile-unrealized-casts",
            "-o",
            llvm_mlir,
        ])
        .status()
        .expect("mlir-opt");
    assert!(status.success());
    let status = Command::new(&mlir_translate)
        .args(["--mlir-to-llvmir", llvm_mlir, "-o", llvm_ir])
        .status()
        .expect("mlir-translate");
    assert!(status.success());
    let status = Command::new(&clang)
        .args([llvm_ir, runtime_c, "-pthread", "-O0", "-o", exe])
        .status()
        .expect("clang");
    assert!(status.success());
}

fn parse_task_tids(stderr: &str) -> std::collections::BTreeSet<String> {
    for part in stderr.split_whitespace() {
        if let Some(value) = part.strip_prefix("ATLI_TASK_TIDS=") {
            return value
                .split(',')
                .filter(|tid| !tid.is_empty())
                .map(ToString::to_string)
                .collect();
        }
    }
    panic!("missing ATLI_TASK_TIDS in {stderr}");
}

fn parse_data_allocs(stderr: &str) -> u64 {
    for part in stderr.split_whitespace() {
        if let Some(value) = part.strip_prefix("ATLI_DATA_ALLOCS=") {
            return value.parse().unwrap();
        }
    }
    panic!("missing ATLI_DATA_ALLOCS in {stderr}");
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

fn parse_tasks_spawned(stderr: &str) -> u64 {
    for part in stderr.split_whitespace() {
        if let Some(value) = part.strip_prefix("ATLI_TASKS_SPAWNED=") {
            return value.parse().unwrap();
        }
    }
    panic!("missing ATLI_TASKS_SPAWNED in {stderr}");
}
