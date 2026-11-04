#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v gh >/dev/null 2>&1; then
  echo 'GitHub CLI is required: brew install gh' >&2
  exit 1
fi
if ! gh auth status >/dev/null 2>&1; then
  echo 'Sign in first with: gh auth login' >&2
  exit 1
fi
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  if [ -n "$(git remote -v)" ]; then
    echo 'This directory already has a Git remote; inspect it before publishing.' >&2
    exit 1
  fi
else
  git init -b main
fi

git add README.md START_HERE_PT.md CITATION.cff CONTRIBUTING.md AGENTS.md lean-toolchain lakefile.toml DiophantineRigidity.lean \
  DiophantineRigidity/ .github/ docs/ scripts/ paper/README.md .gitignore
if ! git diff --cached --quiet; then
  git commit -m 'chore: bootstrap independent Lean formalization project'
fi

echo 'Publishing a PUBLIC repo without the unpublished manuscript files.'
gh repo create DiegoMarquesMath/DiophantineRigidity \
  --public \
  --description 'Formal Verification of Diophantine Rigidity — Lean 4 and mathlib' \
  --source=. --remote=origin --push
