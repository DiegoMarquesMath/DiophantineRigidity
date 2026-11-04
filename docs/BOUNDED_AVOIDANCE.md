# Uniform integer-parameter avoidance: kD bound

This is a proof for the finite-parameter selection underlying
Lemma 4.1 in *Diophantine Rigidity of Analytic Graphs*.

For a set S of at most D roots and nonzero obstruction polynomials
B_ρ(T) over ℂ, all of degree ≤k, there is an integer 0≤t≤kD
such that B_ρ(t)≠0 for every ρ∈S.

The proof is independent of the complex-analytic manuscript:
form the product of obstruction polynomials and apply the
degree bound to kD+1 pairwise distinct integers.

**Remaining:** from the coefficient coprimality hypothesis,
show that for every root ρ of A the polynomial
B_ρ(T)=Σ_{j=0}^k F_j(ρ)T^j is nonzero; verify |S|≤D
via root multiplicities. Then obtain W_t coprime to A.

This certificate does not yet construct W_t or establish any
height bound on its resultant. Full Lemma 4.1 remains open.

## Actual selected polynomial (new CI checkpoint)

`SelectedCombination.lean` builds
`W_t(X)=Σ_{j=0}^k t^j V_j(X)` and a genuine obstruction polynomial
`B_ρ(T)=Σ_{j=0}^k V_j(ρ)T^j`.

For a set S⊂ℂ with |S|≤D and the assumption that at every
ρ∈S some V_j(ρ)≠0, the theorem produces a **single** integer
0≤t≤kD such that W_t(ρ)≠0 at every ρ∈S.

The remaining statement-level bridge identifies S with the complex
root set of A (degree D), verifies no common coefficient zero
from coprimality, and proves the precise integer height estimate
for W_t. This module is not itself the full projective-content lemma.

## Integral auxiliary polynomial and its height (new CI checkpoint)

The new `SelectedIntegerCombination.lean` implements the *actual*
\(W_t\in\mathbb Z[X]\) from the paper and its evaluation in \(\mathbb C\).
Given a finite set of at most D complex points and the non-common-zero
assumption, one integer \(0\le t\le kD\) suffices.

For all X-coefficients \(i\), when \(|[X^i]V_j|\le H\) for
\(0\le j\le k\), the new quantitative theorem proves
\[
|[X^i]W_t|\le (k+1)(kD+1)^k H.
\]
Thus \(H(W_t)\ll_{D,k}H(F)\).

These are precisely the selection and height-control obligations.
**They still do not derive the non-common-zero hypothesis from the
rational gcd condition, nor nonvanishing of Res(A,W_t).**
