set dotenv-load := false

alias v := verify

fmt:
	cargo fmt --check

fmt-fix:
	cargo fmt

test:
	cargo test

clippy:
	cargo clippy --all-targets -- -D warnings

verify: fmt clippy test

audit:
	@git status --short --untracked-files=all | awk '{print $$2}' | grep -E '(^src/parse|^src/parser|^src/type|^src/mlir|^docs/syntax.md)' && \
	  { echo 'Out-of-scope surface detected'; exit 1; } || \
	  echo 'Audit passed: no parser/typechecker/MLIR/surface changes detected.'
