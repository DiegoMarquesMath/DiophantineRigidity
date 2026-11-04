#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for file in paper/ATH_rev.tex paper/ATH_rev.pdf; do
  if [ ! -f "$file" ]; then
    echo "MISSING local source: $file" >&2
    exit 1
  fi
done
shasum -a 256 paper/ATH_rev.tex paper/ATH_rev.pdf
printf '%s\n' 'These files are intentionally Git-ignored. Do not publish them without author approval.'
