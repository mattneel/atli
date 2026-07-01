use atli::core::{Handler, RecursionTag, Term, Type};
use atli::gen::{derive_witness, term_obeys_continuation_usage};
use atli::grade::{Bound, Label};
use atli::interp::{eval, Outcome, Rule};

fn id_lam() -> Term {
    Term::Lam {
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::var("x")),
    }
}

fn identity_handler(op_body: Term) -> Handler {
    Handler {
        return_var: "r".into(),
        return_body: Box::new(Term::var("r")),
        op_label: Label::L,
        op_param: "p".into(),
        op_k: "k".into(),
        op_body: Box::new(op_body),
    }
}

#[test]
fn beta_reduction_for_application() {
    let term = Term::App(Box::new(id_lam()), Box::new(Term::nat(42)));
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(42));
    assert_eq!(report.trace, vec![Rule::Beta]);
}

#[test]
fn let_reduction_substitutes_value() {
    let term = Term::Let {
        var: "x".into(),
        expr: Box::new(Term::nat(7)),
        body: Box::new(Term::var("x")),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(7));
    assert_eq!(report.trace, vec![Rule::Let]);
}

#[test]
fn case_zero_reduces_to_zero_branch() {
    let term = Term::CaseNat {
        scrutinee: Box::new(Term::zero()),
        zero_body: Box::new(Term::nat(10)),
        succ_var: "p".into(),
        succ_body: Box::new(Term::var("p")),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(10));
    assert_eq!(report.trace, vec![Rule::CaseZero]);
}

#[test]
fn case_succ_reduces_with_predecessor_substitution() {
    let term = Term::CaseNat {
        scrutinee: Box::new(Term::succ(Term::nat(2))),
        zero_body: Box::new(Term::zero()),
        succ_var: "p".into(),
        succ_body: Box::new(Term::var("p")),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(2));
    assert_eq!(report.trace, vec![Rule::CaseSucc]);
}

#[test]
fn unhandled_perform_is_intentional_negative_fixture() {
    let report = eval(Term::Perform(Label::L, Box::new(Term::nat(1))), 8, false);
    assert_eq!(report.outcome, Outcome::StuckUnhandledOperation);
}

#[test]
fn handler_return_clause_runs_on_value() {
    let term = Term::Handle {
        body: Box::new(Term::nat(3)),
        handler: identity_handler(Term::nat(0)),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(3));
    assert_eq!(report.trace, vec![Rule::HReturn]);
}

#[test]
fn handler_op_resume_is_deep_and_reinstalls_handler() {
    let body = Term::Let {
        var: "a".into(),
        expr: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        body: Box::new(Term::Perform(Label::L, Box::new(Term::var("a")))),
    };
    let op_body = Term::Resume {
        kont: Box::new(Term::var("k")),
        arg: Box::new(Term::var("p")),
    };
    let term = Term::Handle {
        body: Box::new(body),
        handler: identity_handler(op_body),
    };
    let report = eval(term, 32, false);
    assert_eq!(report.outcome, Outcome::Value, "{report:?}");
    assert_eq!(report.final_term, Term::nat(1));
    assert_eq!(
        report.trace,
        vec![
            Rule::HOp,
            Rule::Resume,
            Rule::Let,
            Rule::HOp,
            Rule::Resume,
            Rule::HReturn
        ]
    );
    assert_eq!(report.max_frame, 1);
}

#[test]
fn handler_op_can_drop_continuation() {
    let term = Term::Handle {
        body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        handler: identity_handler(Term::nat(9)),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(9));
    assert_eq!(report.trace, vec![Rule::HOp]);
}

#[test]
fn dropped_handler_does_not_capture_context_frame() {
    let body = Term::Let {
        var: "a".into(),
        expr: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        body: Box::new(Term::var("a")),
    };
    let term = Term::Handle {
        body: Box::new(body),
        handler: identity_handler(Term::nat(9)),
    };
    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(9));
    assert_eq!(report.trace, vec![Rule::HOp]);
    assert_eq!(report.max_frame, 0);
}

#[test]
fn mention_without_resume_is_negative_checker_obligation() {
    let body = Term::Let {
        var: "a".into(),
        expr: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        body: Box::new(Term::var("a")),
    };
    let op_body = Term::Let {
        var: "z".into(),
        expr: Box::new(Term::var("k")),
        body: Box::new(Term::nat(9)),
    };
    let term = Term::Handle {
        body: Box::new(body),
        handler: identity_handler(op_body),
    };

    assert!(
        !term_obeys_continuation_usage(&term),
        "Sprint 03 checker must reject mention-without-resume handler clauses"
    );
    let witness = derive_witness(&term);
    assert_eq!(witness.bound, Bound::ZERO);

    let report = eval(term, 8, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::nat(9));
    assert_eq!(report.max_frame, 1);
}

#[test]
fn double_resume_is_detected_as_stuck() {
    let op_body = Term::Let {
        var: "_spent".into(),
        expr: Box::new(Term::Resume {
            kont: Box::new(Term::var("k")),
            arg: Box::new(Term::var("p")),
        }),
        body: Box::new(Term::Resume {
            kont: Box::new(Term::var("k")),
            arg: Box::new(Term::var("p")),
        }),
    };
    let term = Term::Handle {
        body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        handler: identity_handler(op_body),
    };
    let report = eval(term, 32, false);
    assert_eq!(report.outcome, Outcome::StuckDoubleResume, "{report:?}");
}

#[test]
fn structural_fix_unfolds_to_terminating_function() {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::CaseNat {
            scrutinee: Box::new(Term::var("x")),
            zero_body: Box::new(Term::zero()),
            succ_var: "pred".into(),
            succ_body: Box::new(Term::App(
                Box::new(Term::var("f")),
                Box::new(Term::var("pred")),
            )),
        }),
        tag: RecursionTag::Structural,
    };
    let report = eval(Term::App(Box::new(fix), Box::new(Term::nat(3))), 32, false);
    assert_eq!(report.outcome, Outcome::Value);
    assert_eq!(report.final_term, Term::zero());
    assert_eq!(
        report.trace,
        vec![
            Rule::Unfold,
            Rule::Beta,
            Rule::CaseSucc,
            Rule::Unfold,
            Rule::Beta,
            Rule::CaseSucc,
            Rule::Unfold,
            Rule::Beta,
            Rule::CaseSucc,
            Rule::Unfold,
            Rule::Beta,
            Rule::CaseZero,
        ]
    );
}

#[test]
fn divergent_fix_exhausts_budget_when_tagged_div() {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::App(
            Box::new(Term::var("f")),
            Box::new(Term::var("x")),
        )),
        tag: RecursionTag::Div,
    };
    let report = eval(Term::App(Box::new(fix), Box::new(Term::nat(0))), 8, true);
    assert_eq!(report.outcome, Outcome::BudgetExhaustedDiv);
    assert!(report.trace.contains(&Rule::Unfold));
}
