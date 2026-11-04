# Integration record — 2026-11-04

## Why this branch exists

The repository's public `main` contained primarily a bootstrap, whereas substantive Lean formalization had accumulated on open development PRs. This branch restores those results without pretending they have already proved the full manuscript.

## Provenance

- **Foundation:** based on the head of [PR #10](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/10), commit `84f8fc5041899d20a7e9aa8f588d808e881e1f1d`, successful [CI run 41851694299](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41851694299). This commit contains the stacked arithmetic, Bézout, projective-reflection, avoidance, Sylvester and kernel modules.
- **Recovered from PR #9:** `DiophantineRigidity/RationalCoefficientCoprimality.lean` and `docs/RATIONAL_COEFFICIENT_GCD.md`. Original commit `1738c9db83820b1c19a9913cffcc9a2867e5f402`, successful [CI run 41850220738](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41850220738).
- **Recovered from PR #11:** `DiophantineRigidity/ResultantBaseChange.lean` and `docs/RESULTANT_BASE_CHANGE.md`. Original commit `6e6dd5e7487e7971f0f5c1646f0eb33f143910ce`, successful [CI run 41852264160](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41852264160).
- **Recovered from PR #12:** `DiophantineRigidity/WitnessMonotonicity.lean`, original commit `0a6d19bd302241a8c7b6b089db70c173d9e6fc57`; integrated code must pass fresh CI.
- **Legacy dependency:** [MahlerLean](https://github.com/DiegoMarquesMath/MahlerLean) is kept pinned in `lakefile.toml`. Its older entire-rigidity/Cantor formalizations are reused only through exact imports, not copied or relabeled as new results. Its open [PR #4](https://github.com/DiegoMarquesMath/MahlerLean/pull/4) contains a parallel draft formalization scaffold, not additional certified main research theorems.

The library root imports all recovered modules, while `scripts/Audit.lean` explicitly reports their axiom dependencies. No source theorem was replaced by an assumed equivalent statement.

## Why no automatic merge of old PRs

The old PRs form a **partially stacked, partially diverging graph**: PRs #7 and #8 build on #6, #10 builds on #8, #9 branches from #7, and #11 branches from #5. Blindly merging them in number order risks conflicts and regressions. A single integration branch based on #10 with the distinct #9/#11 modules directly recovered preserves the largest coherent compiled base.

## What is still not included

Uncommitted local files under `~/Developer/MahlerLeanATH` (and the revised manuscript under `paper/`) are **not remotely readable via GitHub**. Do not claim they were migrated. To integrate them, supply source files or push a review branch. Never upload unpublished manuscript material without explicit authorization.

## Verification standard

After the integration PR is created, its combined GitHub Actions run is the authoritative compilation/axiom-audit result for the integration commit. Earlier green PRs are supporting provenance, not a substitute for that check.

## Next mathematical gate

The partial projective-content Lemma 4.1 needs its remaining uniform quantitative estimates, notably the precise Bézout height/congruence control, p-adic covering and divisor summation. This must be compared with the revised manuscript before certifying the lemma. The new general two-height theorem, S-number Cantor theorem and arithmetic descent remain future obligations.
