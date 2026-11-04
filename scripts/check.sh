#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Basic source-policy guard; it supplements, but never replaces, kernel checking.
if grep -nE '(^|[[:space:]])(sorry|admit|axiom|opaque|unsafe|native_decide)([[:space:]]|$)' \
    DiophantineRigidity.lean DiophantineRigidity/*.lean; then
  echo 'Unapproved proof shortcut in project source.' >&2
  exit 1
fi

lake build DiophantineRigidity
for file in DiophantineRigidity/*.lean; do
  lake env lean -DwarningAsError=true "$file"
done

log_file="$(mktemp -t dr-axioms.XXXXXX)"
trap 'rm -f "$log_file"' EXIT
lake env lean -DwarningAsError=true scripts/Audit.lean | tee "$log_file"
python3 - "$log_file" <<'PYINNER'
import re, sys
from pathlib import Path
log = Path(sys.argv[1]).read_text()
if 'sorryAx' in log:
    raise SystemExit('ERROR: axiom audit includes sorryAx')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log):
    bad = [x.strip() for x in group.split(',') if x.strip() and x.strip() not in allowed]
    if bad:
        raise SystemExit('ERROR: unapproved axiom(s): ' + ', '.join(bad))
for name in ('mem_exceptionalArguments', 'reducedRationalSpacing', 'entireRigidityFromLegacy'):
    if name not in log:
        raise SystemExit('ERROR: missing axiom report for ' + name)
print('Axiom output examined: only permitted logical foundations detected.')
PYINNER

echo 'SUCCESS: current DiophantineRigidity declarations passed the configured checks.'
echo 'Note: the new research theorems are not yet formalized.'
