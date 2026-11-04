# Arithmetic foundations — formalization checkpoint

**Branch:** `proofs/arithmetic-foundations`  
**Manuscript:** *Diophantine Rigidity of Analytic Graphs*, Sections 2–4.  
**Verification status:** source definitions and proofs submitted; no claim of
successful validation until GitHub Actions completes and is inspected.

## Newly written Lean declarations

- `DiophantineRigidity.clearedEvaluation` is the integral expression
  \(\sum_{i=0}^{D} a_i p^i q^{D-i}\).
- `clearedEvaluation_spec` proves that it equals
  \(q^D P(p/q)\), for every integer polynomial \(P\) of degree at most
  \(D\) and every nonzero integer \(q\).
- `exists_integer_cleared_evaluation` packages the integral witness.
- `exists_integer_cleared_coefficient` lifts the fact to each
  \(Y\)-coefficient of \(F\in\mathbb Z[X,Y]\), using
  `Polynomial (Polynomial ℤ)` with outer variable \(Y\).
- `farey_interval_bound` and `farey_union_bound` expose equation (2.3)
  through existing **previously formalized** MahlerLean theorems.

## What is *not* proved by these declarations

- A bound for contents of the integer coefficient polynomial
  \(q^D F(p/q,Y)\).
- The two-chart \(p\)-adic argument of Lemma 4.1.
- The integral kernel and Hankel reconstruction of Lemmas 3.1–3.2.
- The resultant inequality of Lemma 4.2.
- The multiscale propagation of Lemma 5.1.
- The main two-height count or S-number/Cantor/descent theorems.

These remain explicit obligations and cannot be certified by
compiling this checkpoint alone.

## Evidence required

Run `bash scripts/check.sh` with pinned Lean 4.24.0 and inspect the
`#print axioms` output of the declarations above. The exact
manuscript-to-Lean statement correspondence for the revised TeX is
a separate review.
