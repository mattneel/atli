#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
import re
import sys

learning = Path('book/src/learning')
errors: list[str] = []
include_re = re.compile(r"\{\{#include\s+([^}\s]+)")

for path in sorted(learning.glob('*.md')):
    lines = path.read_text().splitlines()
    in_fence = False
    fence_lang: str | None = None
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith('```'):
            if not in_fence:
                in_fence = True
                fence_lang = stripped[3:].split(',', 1)[0].strip()
                if fence_lang == 'atli':
                    errors.append(f"{path}:{idx}: tutorial samples use the Zig highlighter until Atli has one; use ```zig")
            else:
                in_fence = False
                fence_lang = None
            continue

        match = include_re.search(line)
        if not match:
            continue
        target = match.group(1)
        if target.endswith('.atli') or '.atli:' in target:
            if not in_fence:
                errors.append(f"{path}:{idx}: Atli include is rendered as prose; wrap it in a fenced ```zig block")
            elif fence_lang != 'zig':
                errors.append(f"{path}:{idx}: Atli include must be in a ```zig fence, found ```{fence_lang or ''}")
            if not target.startswith('../../../examples/'):
                errors.append(f"{path}:{idx}: tutorial Atli include must come from examples/, found {target}")

html_root = Path('book/book/learning')
if html_root.exists():
    for path in sorted(learning.glob('*.md')):
        src = path.read_text()
        atli_include_count = sum(
            1 for m in include_re.finditer(src)
            if m.group(1).endswith('.atli') or '.atli:' in m.group(1)
        )
        if atli_include_count == 0:
            continue
        html_path = html_root / (path.stem + '.html')
        if not html_path.exists():
            errors.append(f"{html_path}: missing built page; run mdbook build book before this check")
            continue
        html = html_path.read_text()
        code_count = html.count('class="language-zig"')
        if code_count < atli_include_count:
            errors.append(
                f"{html_path}: expected at least {atli_include_count} Zig-highlighted code block(s), found {code_count}"
            )
        if '{{#include' in html:
            errors.append(f"{html_path}: raw mdBook include directive leaked into rendered HTML")
else:
    errors.append('book/book/learning does not exist; run mdbook build book before this check')

if errors:
    print('Book sample no-rot check failed:', file=sys.stderr)
    for error in errors:
        print(f'  - {error}', file=sys.stderr)
    sys.exit(1)

print('Book sample no-rot check OK')
PY
