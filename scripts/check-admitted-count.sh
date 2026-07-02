#!/usr/bin/env bash
set -euo pipefail
expected=$(tr -d '[:space:]' < proofs/ADMITTED_COUNT)
actual=$(grep -R "Admitted\." -n proofs/theories/*.v | wc -l | tr -d '[:space:]')
if [[ "$actual" != "$expected" ]]; then
  echo "Admitted count changed: expected $expected, found $actual" >&2
  echo "Update proofs/ADMITTED_COUNT in the same commit for any deliberate ledger move (up or down)." >&2
  exit 1
fi
echo "Admitted count OK: $actual"
