//! Property harness for generated reduced-core terms.
//!
//! These tests are the Sprint 01 empirical checks for `docs/calculus.md §8` obligations.

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::test_runner::{Config, RngSeed, TestRunner};

    use crate::core::{CoverageTag, Divergence, GeneratedTerm};
    use crate::gen::{
        coverage_counts, fixed_seed_sample, generated_case, FIXED_SEED, REQUIRED_COVERAGE,
        SAMPLE_SIZE, STEP_BUDGET,
    };
    use crate::grade::Bound;
    use crate::interp::{classify_progress, eval, Outcome};

    fn generated_strategy() -> impl Strategy<Value = GeneratedTerm> {
        any::<u8>().prop_map(generated_case)
    }

    fn assert_acceptance(generated: GeneratedTerm) {
        let progress = classify_progress(generated.term.clone());
        assert!(
            matches!(progress, Outcome::Value | Outcome::Stepable),
            "progress failed for {}: {progress:?}: {}",
            generated.name,
            generated.term
        );

        let expect_div = generated.witness.divergence == Divergence::Div;
        let first = eval(generated.term.clone(), STEP_BUDGET, expect_div);
        let second = eval(generated.term.clone(), STEP_BUDGET, expect_div);
        assert_eq!(
            first.normalized_for_determinism(),
            second.normalized_for_determinism(),
            "determinism failed for {}",
            generated.name
        );

        assert_ne!(
            first.outcome,
            Outcome::StuckDoubleResume,
            "one-shot soundness failed for {}",
            generated.name
        );
        assert_ne!(
            first.outcome,
            Outcome::StuckUnhandledOperation,
            "handled operation escaped for {}",
            generated.name
        );
        assert_ne!(
            first.outcome,
            Outcome::InternalMalformed,
            "unexpected internal malformed state for {}: {first:?}",
            generated.name
        );

        match generated.witness.divergence {
            Divergence::Terminates => assert_eq!(
                first.outcome,
                Outcome::Value,
                "terminating generated term exhausted budget or stuck: {} -> {first:?}",
                generated.name
            ),
            Divergence::Div => assert_eq!(
                first.outcome,
                Outcome::BudgetExhaustedDiv,
                "div generated term should be classified by budget exhaustion"
            ),
        }

        if let Bound::Finite(bound) = generated.witness.bound {
            assert!(
                first.max_frame <= bound,
                "boundedness failed for {}: max_frame {} > β {}",
                generated.name,
                first.max_frame,
                bound
            );
        }

        assert!(generated.witness.region.outlives(generated.witness.region));
        assert!(
            generated.witness.continuation_uses.resumed
                <= generated.witness.continuation_uses.introduced,
            "witness permits multi-shot continuation use"
        );
    }

    #[test]
    fn generated_terms_satisfy_acceptance_properties_with_fixed_seed() {
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
            .expect("fixed-seed generated acceptance properties pass");
    }

    #[test]
    fn fixed_seed_sample_covers_every_required_form() {
        let sample = fixed_seed_sample();
        assert_eq!(sample.len(), SAMPLE_SIZE);
        let counts = coverage_counts(&sample);
        assert!(counts.all_required_present(), "coverage counts: {counts:?}");
        for tag in REQUIRED_COVERAGE {
            assert!(counts.get(tag) > 0, "missing coverage for {tag:?}");
        }
        assert!(counts.get(CoverageTag::LambdaApp) > 0);
    }

    #[test]
    fn generated_witnesses_are_complete_and_shrinker_regenerates_them() {
        // The proptest input shrinks the `u8` selector; each shrink maps through
        // `generated_case`, so the witness is regenerated from the shrunk term constructor.
        for selector in 0_u8..32 {
            let generated = generated_case(selector);
            assert!(!generated.name.is_empty());
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
}
