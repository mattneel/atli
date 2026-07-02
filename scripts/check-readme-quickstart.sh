#!/usr/bin/env bash
set -euo pipefail
expected_run='55'
actual_run=$(cargo run --quiet -- run examples/fib.atli)
if [[ "$actual_run" != "$expected_run" ]]; then
  echo "README quickstart run mismatch: expected '$expected_run', got '$actual_run'" >&2
  exit 1
fi
expected_check=$'type: Nat\neffects: ∅\nβ: 2\ndivergence: Terminates'
actual_check=$(cargo run --quiet -- check examples/fib.atli)
if [[ "$actual_check" != "$expected_check" ]]; then
  echo "README quickstart check mismatch" >&2
  diff -u <(printf '%s\n' "$expected_check") <(printf '%s\n' "$actual_check") >&2 || true
  exit 1
fi
expected_compiled_stdout='55'
compiled_stdout=$(mktemp)
compiled_stderr=$(mktemp)
cargo run --quiet -- run --compiled examples/fib.atli >"$compiled_stdout" 2>"$compiled_stderr"
if [[ "$(cat "$compiled_stdout")" != "$expected_compiled_stdout" ]]; then
  echo "README compiled quickstart stdout mismatch" >&2
  cat "$compiled_stdout" >&2
  exit 1
fi
expected_compiled_stderr='ATLI_HIGH_WATER=1 ATLI_BETA=2 ATLI_DATA_ALLOCS=0'
if [[ "$(cat "$compiled_stderr")" != "$expected_compiled_stderr" ]]; then
  echo "README compiled quickstart stderr mismatch" >&2
  diff -u <(printf '%s\n' "$expected_compiled_stderr") "$compiled_stderr" >&2 || true
  exit 1
fi
rm -f "$compiled_stdout" "$compiled_stderr"

if grep -q 'β: 1' README.md docs/sprint-10-report.md; then
  echo "stale quickstart beta found in docs" >&2
  exit 1
fi
echo "README quickstart OK"
