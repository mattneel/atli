# Contributing to Atli

## Completion contract

- Every acceptance criterion is binding. There is no BLOCKED status in sprint reports.
- Recording a `SPEC-GAP:` or finding is mandatory when discovered, but recording never discharges a criterion. Resolve conservatively and deliver.
- If a criterion is genuinely impossible, halt immediately and produce the impossibility argument as the sole output. Do not ship a partial sprint around it.

## Spec-gap protocol

Ambiguity in `docs/calculus.md`, `docs/syntax.md`, or `docs/elaboration.md` gets a `SPEC-GAP:` entry in `docs/spec-gaps.md`, a conservative implementation choice, and a report note. Resolved gaps move to the resolved ledger with the commit rationale.

## Found-a-bug discipline

Findings in verified components require a separate commit, a golden or property that would have caught the bug, and a report entry. Do not silently align the oracle, checker, generator, proofs, or backend to each other.

## Golden rule

Constructors may adapt as the representation grows; semantic assertions are immutable. Existing goldens are regression anchors.

## Canonical ripple order

Rules → core AST → interpreter → derive/generator → checker/solver → proofs ledger → surface/elaboration → codegen → docs/report.

## Commit granularity

One logical unit per commit. Keep the tree green at every commit. Run `cargo fmt --check`, `cargo clippy --all-targets -- -D warnings`, `cargo test`, `make -C proofs`, `scripts/check-admitted-count.sh`, `cargo run -- test examples/`, and the Book checks before release.

## Report format

Each sprint report records acceptance status, verification commands, findings, gaps, generated statistics where relevant, and carried-forward work.

## Branch protection recommendation

Protect `master` with the CI gate required, including the proof build, admitted-count check, example differential, and Book build. GitHub Pages should use Source = GitHub Actions.
