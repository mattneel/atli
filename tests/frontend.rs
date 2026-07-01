use std::fs;
use std::process::Command;

use atli::check::check;
use atli::core::{Handler, Term};
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
        handler: Handler {
            return_var: "x".into(),
            return_body: Box::new(Term::var("x")),
            op_label: Label::L,
            op_param: "p".into(),
            op_k: "k".into(),
            op_body: Box::new(Term::Resume {
                kont: Box::new(Term::var("k")),
                arg: Box::new(Term::var("p")),
            }),
        },
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
        handler: Handler {
            return_var: "x".into(),
            return_body: Box::new(Term::var("x")),
            op_label: Label::L,
            op_param: "p".into(),
            op_k: "_k".into(),
            op_body: Box::new(Term::nat(9)),
        },
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
    assert!(stderr.contains("examples/wedge.atli:6:9"));
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
    assert!(stderr.contains("examples/unsupported.atli:1:11"));
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
