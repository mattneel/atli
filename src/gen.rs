//! Well-typed-by-construction term generator for Sprint 01.
//!
//! The generator is deliberately small and witness-producing. It follows the typing rules
//! as generation rules (`docs/calculus.md §4`) for the reduced target (`§10`) rather than
//! depending on a type checker, which is out of scope for Sprint 01.

use std::collections::BTreeSet;

use crate::core::{
    ContinuationUseFacts, CoverageTag, Divergence, GeneratedTerm, Handler, RecursionTag, Term,
    Type, Witness,
};
use crate::grade::{Bound, Eff, Label, Region};

pub const FIXED_SEED: u64 = 0xA711_0001;
pub const SAMPLE_SIZE: usize = 128;
pub const STEP_BUDGET: usize = 64;

#[must_use]
pub fn generated_case(selector: u8) -> GeneratedTerm {
    match selector % 8 {
        0 => unit_case(),
        1 => lambda_app_case(u64::from(selector)),
        2 => let_case(u64::from(selector)),
        3 => handle_resuming_case(),
        4 => handle_dropped_case(),
        5 => structural_fix_case(),
        6 => measured_fix_case(),
        _ => div_fix_case(),
    }
}

#[must_use]
pub fn fixed_seed_sample() -> Vec<GeneratedTerm> {
    // Deterministic LCG over selectors. The fixed seed is reported in the sprint report and
    // is intentionally independent of proptest internals for stable coverage accounting.
    let mut state = FIXED_SEED;
    let mut sample = (0_u8..8).map(generated_case).collect::<Vec<_>>();
    while sample.len() < SAMPLE_SIZE {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        sample.push(generated_case((state >> 32) as u8));
    }
    sample
}

#[must_use]
pub fn coverage_counts(sample: &[GeneratedTerm]) -> BTreeMapCounts {
    let mut counts = BTreeMapCounts::default();
    for generated in sample {
        for tag in &generated.witness.coverage {
            counts.increment(*tag);
        }
    }
    counts
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BTreeMapCounts(std::collections::BTreeMap<CoverageTag, usize>);

impl BTreeMapCounts {
    pub fn increment(&mut self, tag: CoverageTag) {
        *self.0.entry(tag).or_default() += 1;
    }

    #[must_use]
    pub fn get(&self, tag: CoverageTag) -> usize {
        self.0.get(&tag).copied().unwrap_or(0)
    }

    #[must_use]
    pub fn all_required_present(&self) -> bool {
        REQUIRED_COVERAGE.iter().all(|tag| self.get(*tag) > 0)
    }
}

pub const REQUIRED_COVERAGE: [CoverageTag; 7] = [
    CoverageTag::LambdaApp,
    CoverageTag::Let,
    CoverageTag::FixStructural,
    CoverageTag::FixMeasure,
    CoverageTag::Perform,
    CoverageTag::HandleResuming,
    CoverageTag::HandleDropped,
];

fn unit_case() -> GeneratedTerm {
    generated(
        "unit",
        Term::unit(),
        Type::Unit,
        Bound::ZERO,
        &[],
        Divergence::Terminates,
        0,
        0,
        0,
    )
}

fn lambda_app_case(value: u64) -> GeneratedTerm {
    let term = Term::App(
        Box::new(Term::Lam {
            param: "x".into(),
            param_ty: Type::Nat,
            body: Box::new(Term::var("x")),
        }),
        Box::new(Term::nat(value % 17)),
    );
    generated(
        "lambda_app",
        term,
        Type::Nat,
        Bound::ZERO,
        &[CoverageTag::LambdaApp],
        Divergence::Terminates,
        0,
        0,
        0,
    )
}

fn let_case(value: u64) -> GeneratedTerm {
    let term = Term::Let {
        var: "x".into(),
        expr: Box::new(Term::nat(value % 23)),
        body: Box::new(Term::var("x")),
    };
    generated(
        "let",
        term,
        Type::Nat,
        Bound::ZERO,
        &[CoverageTag::Let],
        Divergence::Terminates,
        0,
        0,
        0,
    )
}

fn handle_resuming_case() -> GeneratedTerm {
    let body = Term::Let {
        var: "a".into(),
        expr: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
        body: Box::new(Term::var("a")),
    };
    let op_body = Term::Resume {
        kont: Box::new(Term::var("k")),
        arg: Box::new(Term::var("p")),
    };
    generated(
        "handle_resuming",
        Term::Handle {
            body: Box::new(body),
            handler: identity_handler(op_body),
        },
        Type::Nat,
        Bound::finite(1),
        &[
            CoverageTag::Let,
            CoverageTag::Perform,
            CoverageTag::HandleResuming,
        ],
        Divergence::Terminates,
        1,
        1,
        0,
    )
}

fn handle_dropped_case() -> GeneratedTerm {
    generated(
        "handle_dropped",
        Term::Handle {
            body: Box::new(Term::Perform(Label::L, Box::new(Term::nat(1)))),
            handler: identity_handler(Term::nat(9)),
        },
        Type::Nat,
        Bound::ZERO,
        &[CoverageTag::Perform, CoverageTag::HandleDropped],
        Divergence::Terminates,
        1,
        0,
        1,
    )
}

fn structural_fix_case() -> GeneratedTerm {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::var("x")),
        tag: RecursionTag::Structural,
    };
    generated(
        "structural_fix",
        Term::App(Box::new(fix), Box::new(Term::nat(4))),
        Type::Nat,
        Bound::finite(1),
        &[CoverageTag::FixStructural],
        Divergence::Terminates,
        0,
        0,
        0,
    )
}

fn measured_fix_case() -> GeneratedTerm {
    let fix = Term::Fix {
        func: "f".into(),
        param: "x".into(),
        param_ty: Type::Nat,
        body: Box::new(Term::var("x")),
        tag: RecursionTag::Measure,
    };
    generated(
        "measured_fix",
        Term::App(Box::new(fix), Box::new(Term::nat(6))),
        Type::Nat,
        Bound::finite(1),
        &[CoverageTag::FixMeasure],
        Divergence::Terminates,
        0,
        0,
        0,
    )
}

fn div_fix_case() -> GeneratedTerm {
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
    generated(
        "div_fix",
        Term::App(Box::new(fix), Box::new(Term::nat(0))),
        Type::Nat,
        Bound::Omega,
        &[],
        Divergence::Div,
        0,
        0,
        0,
    )
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

#[allow(clippy::too_many_arguments)]
fn generated(
    name: &'static str,
    term: Term,
    ty: Type,
    bound: Bound,
    coverage: &[CoverageTag],
    divergence: Divergence,
    introduced: u32,
    resumed: u32,
    dropped: u32,
) -> GeneratedTerm {
    let coverage = coverage.iter().copied().collect::<BTreeSet<_>>();
    GeneratedTerm {
        term,
        name,
        witness: Witness {
            ty,
            effects: Eff::empty(),
            bound,
            region: Region::Arena,
            continuation_uses: ContinuationUseFacts {
                introduced,
                resumed,
                dropped,
            },
            divergence,
            coverage,
        },
    }
}
