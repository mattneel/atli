#!/usr/bin/env bash
set -euo pipefail
if grep -R "^\`\`\`atli" -n book/src/learning 2>/dev/null; then
  echo "Tutorial Atli samples must use mdBook {{#include}} from examples/, not fenced atli blocks." >&2
  exit 1
fi
echo "Book sample no-rot check OK"
