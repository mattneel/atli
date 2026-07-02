//! Differential property harness for generated reduced-core terms.
//!
//! These tests are the Sprint 02/Sprint 03 empirical checks for `docs/calculus.md §8`: generated
//! terms are built by a type-directed choice-sequence generator, witnesses are re-derived
//! structurally, and the interpreter independently measures realized behavior.

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::test_runner::{Config, RngSeed, TestRunner};

    use crate::check::check;
    use crate::core::{CoverageTag, Divergence, ExpectedOutcome, GeneratedTerm};
    use crate::elaborate::elaborate_program;
    use crate::gen::{
        aggregate_negative_fixtures, coverage_counts, derive_witness, distribution,
        fixed_seed_sample, generated_from_choices, FIXED_SEED, MAX_CHOICES, REQUIRED_COVERAGE,
        SAMPLE_SIZE, STEP_BUDGET,
    };
    use crate::grade::Bound;
    use crate::interp::{classify_progress, eval, Outcome};
    use crate::surface::parse_program;

    fn generated_strategy() -> impl Strategy<Value = GeneratedTerm> {
        prop::collection::vec(any::<u8>(), 1..=MAX_CHOICES).prop_map(generated_from_choices)
    }

    fn assert_acceptance(generated: GeneratedTerm) {
        let seed = FIXED_SEED;
        let rederived = derive_witness(&generated.term);
        assert_eq!(
            generated.witness, rederived,
            "seed {seed:#x}: stale witness for {}: {}",
            generated.name, generated.term
        );
        assert!(
            generated.witness.continuation_uses.resumed
                <= generated.witness.continuation_uses.introduced,
            "seed {seed:#x}: affine witness violation for {}: {}",
            generated.name,
            generated.term
        );

        let expect_div = generated.witness.divergence == Divergence::Div;
        let first = eval(generated.term.clone(), STEP_BUDGET, expect_div);
        let second = eval(generated.term.clone(), STEP_BUDGET, expect_div);
        assert_eq!(
            first.normalized_for_determinism(),
            second.normalized_for_determinism(),
            "seed {seed:#x}: determinism failed for {}: {}",
            generated.name,
            generated.term
        );

        if generated.expected == ExpectedOutcome::UnhandledOperation {
            assert_eq!(
                classify_progress(generated.term.clone()),
                Outcome::StuckUnhandledOperation,
                "seed {seed:#x}: negative perform fixture should be immediately stuck: {}",
                generated.term
            );
            assert_eq!(
                first.outcome,
                Outcome::StuckUnhandledOperation,
                "seed {seed:#x}: negative perform fixture did not detect unhandled operation"
            );
            return;
        }

        let checked = check(&generated.term).unwrap_or_else(|err| {
            panic!(
                "seed {seed:#x}: checker rejected safe generated term {}: {err}: {}",
                generated.name, generated.term
            )
        });
        assert_eq!(
            checked.witness(),
            &generated.witness,
            "seed {seed:#x}: checker/derive witness disagreement for {}: {}",
            generated.name,
            generated.term
        );

        let progress = classify_progress(generated.term.clone());
        assert!(
            matches!(progress, Outcome::Value | Outcome::Stepable),
            "seed {seed:#x}: progress failed for {}: {progress:?}: {}",
            generated.name,
            generated.term
        );

        assert_ne!(
            first.outcome,
            Outcome::StuckDoubleResume,
            "seed {seed:#x}: one-shot soundness failed for {}: {}",
            generated.name,
            generated.term
        );
        assert_ne!(
            first.outcome,
            Outcome::StuckUnhandledOperation,
            "seed {seed:#x}: handled operation escaped for {}: {}",
            generated.name,
            generated.term
        );
        assert_ne!(
            first.outcome,
            Outcome::InternalMalformed,
            "seed {seed:#x}: unexpected internal malformed state for {}: {first:?}: {}",
            generated.name,
            generated.term
        );

        match generated.witness.divergence {
            Divergence::Terminates => assert_eq!(
                first.outcome,
                Outcome::Value,
                "seed {seed:#x}: terminating generated term exhausted budget or stuck: {} -> {first:?}: {}",
                generated.name,
                generated.term
            ),
            Divergence::Div => assert_eq!(
                first.outcome,
                Outcome::BudgetExhaustedDiv,
                "seed {seed:#x}: div generated term should exhaust budget: {}",
                generated.term
            ),
        }

        if let Bound::Finite(bound) = checked.witness().bound {
            assert!(
                first.max_frame <= bound,
                "seed {seed:#x}: checker-certified boundedness failed for {}: max_frame {} > β {}: {}",
                generated.name,
                first.max_frame,
                bound,
                generated.term
            );
        }
    }

    #[test]
    fn generated_terms_satisfy_differential_acceptance_with_fixed_seed() {
        let mut runner = TestRunner::new(Config {
            cases: SAMPLE_SIZE as u32,
            rng_seed: RngSeed::Fixed(FIXED_SEED),
            failure_persistence: None,
            ..Config::default()
        });
        runner
            .run(&generated_strategy(), |generated| {
                assert_acceptance(generated);
                Ok(())
            })
            .expect("fixed-seed generated differential properties pass");
    }

    #[test]
    fn fixed_seed_sample_has_required_coverage_and_distribution() {
        let sample = fixed_seed_sample();
        assert_eq!(sample.len(), SAMPLE_SIZE);
        let counts = coverage_counts(&sample);
        assert!(counts.all_required_present(), "coverage counts: {counts:?}");
        for tag in REQUIRED_COVERAGE {
            assert!(counts.get(tag) > 0, "missing coverage for {tag:?}");
        }
        assert!(counts.get(CoverageTag::LambdaApp) > 0);
        assert!(
            counts.get(CoverageTag::Array) > 0,
            "missing array/uniqueness coverage"
        );
        for tag in [
            CoverageTag::RecordAggregate,
            CoverageTag::VariantAggregate,
            CoverageTag::DestructureConsume,
            CoverageTag::RecordFunctionalUpdate,
            CoverageTag::RecordInplaceUpdate,
            CoverageTag::ConstructorPatternDescent,
            CoverageTag::Scope,
            CoverageTag::Spawn,
            CoverageTag::Await,
            CoverageTag::GenericInstantiation,
            CoverageTag::PreserveUnique,
            CoverageTag::PreserveShared,
        ] {
            assert!(
                counts.get(tag) > 0,
                "missing aggregate/generic generator coverage for {tag:?}: {counts:?}"
            );
        }

        let distribution = distribution(&sample);
        assert!(
            distribution.nested_handlers > 0,
            "nested-handler count must be nonzero: {distribution:?}"
        );
        assert!(
            distribution.strict_rec_calls > 0,
            "strict recursive-call count must be nonzero: {distribution:?}"
        );
        assert!(
            distribution.non_strict_rec_calls > 0,
            "non-strict recursive-call count must be nonzero: {distribution:?}"
        );
        assert!(
            distribution.negative_unhandled > 0,
            "negative unhandled perform fixtures must be generated"
        );

        let mut frame_positive = 0;
        let mut tight_hits = 0;
        let mut scc_histogram = std::collections::BTreeMap::new();
        for generated in &sample {
            let expect_div = generated.witness.divergence == Divergence::Div;
            let report = eval(generated.term.clone(), STEP_BUDGET, expect_div);
            if generated.expected == ExpectedOutcome::Safe {
                let checked = check(&generated.term).expect("fixed sample checks");
                for size in &checked.solver_stats().scc_sizes {
                    *scc_histogram.entry(*size).or_insert(0usize) += 1;
                }
            }
            if report.max_frame > 0 {
                frame_positive += 1;
            }
            if let Bound::Finite(bound) = generated.witness.bound {
                if report.max_frame == bound {
                    tight_hits += 1;
                }
            }
        }
        assert!(
            frame_positive >= 100,
            "expected ≥100 frame-positive cases, got {frame_positive}"
        );
        assert!(
            tight_hits > 0,
            "expected at least one tight max_frame == β hit"
        );
        assert!(
            scc_histogram.keys().any(|size| *size >= 2),
            "generated sample must include natural multi-node SCCs: {scc_histogram:?}"
        );
    }

    #[test]
    fn aggregate_coverage_assertion_is_falsifiable_when_aggregate_cases_are_disabled() {
        let sample: Vec<_> = (0..SAMPLE_SIZE)
            .map(|case| generated_from_choices(vec![(case % 15) as u8, 3, 5, 8, 13]))
            .collect();
        let counts = coverage_counts(&sample);
        for tag in [
            CoverageTag::RecordAggregate,
            CoverageTag::VariantAggregate,
            CoverageTag::DestructureConsume,
            CoverageTag::RecordFunctionalUpdate,
            CoverageTag::RecordInplaceUpdate,
            CoverageTag::ConstructorPatternDescent,
            CoverageTag::GenericInstantiation,
            CoverageTag::PreserveUnique,
            CoverageTag::PreserveShared,
        ] {
            assert_eq!(
                counts.get(tag),
                0,
                "aggregate/generic tag {tag:?} should disappear when aggregate/generic generators are disabled: {counts:?}"
            );
        }
    }

    #[test]
    fn generated_witnesses_are_complete_and_shrinker_regenerates_them() {
        // The proptest input shrinks choice bytes; every shrink maps through
        // `generated_from_choices`, so the term is rebuilt and the witness is re-derived.
        for selector in 0_u8..64 {
            let generated = generated_from_choices(vec![selector; MAX_CHOICES]);
            assert!(!generated.name.is_empty());
            assert_eq!(generated.witness, derive_witness(&generated.term));
            assert!(generated
                .witness
                .effects
                .is_subset(&generated.witness.effects));
            assert!(matches!(
                generated.witness.ty,
                crate::core::Type::Unit | crate::core::Type::Nat
            ));
            assert!(
                generated.witness.continuation_uses.resumed
                    <= generated.witness.continuation_uses.introduced
            );
        }
    }

    #[test]
    fn generator_tagged_aggregate_negatives_match_frontend_verdicts() {
        for fixture in aggregate_negative_fixtures() {
            let program = parse_program(fixture.source).unwrap_or_else(|err| {
                panic!(
                    "aggregate negative fixture {} should parse before rejection: {err:?}",
                    fixture.name
                )
            });
            let rendered = match elaborate_program(&program) {
                Ok(elaborated) => check(&elaborated.term)
                    .map(|_| String::new())
                    .unwrap_err()
                    .to_string(),
                Err(error) => format!("{error:?}"),
            };
            assert!(
                !rendered.is_empty(),
                "fixture {} must reject in elaboration or checking",
                fixture.name
            );
            assert!(
                rendered.contains(fixture.expected_error),
                "fixture {} rejected with unexpected diagnostic:\nexpected substring: {}\nactual: {}",
                fixture.name,
                fixture.expected_error,
                rendered
            );
        }
    }

    #[test]
    fn nat_case_strict_descent_gives_structural_fix_finite_beta() {
        let fix = crate::core::Term::Fix {
            func: "f".into(),
            param: "x".into(),
            param_ty: crate::core::Type::Nat,
            body: Box::new(crate::core::Term::CaseNat {
                scrutinee: Box::new(crate::core::Term::var("x")),
                zero_body: Box::new(crate::core::Term::zero()),
                succ_var: "pred".into(),
                succ_body: Box::new(crate::core::Term::App(
                    Box::new(crate::core::Term::var("f")),
                    Box::new(crate::core::Term::var("pred")),
                )),
            }),
            tag: crate::core::RecursionTag::Structural,
        };
        let witness = derive_witness(&fix);
        assert_eq!(witness.bound, Bound::finite(1));
    }

    #[test]
    fn non_strict_structural_fix_derives_omega_beta() {
        let fix = crate::core::Term::Fix {
            func: "f".into(),
            param: "x".into(),
            param_ty: crate::core::Type::Nat,
            body: Box::new(crate::core::Term::App(
                Box::new(crate::core::Term::var("f")),
                Box::new(crate::core::Term::var("x")),
            )),
            tag: crate::core::RecursionTag::Structural,
        };
        let witness = derive_witness(&fix);
        assert_eq!(witness.bound, Bound::Omega);
        assert_eq!(witness.divergence, Divergence::Div);
    }
}
