# Integral Sylvester certificate — high-priority proof obligation

This module builds on the verified two-chart projective-content bridge.

## New theorem

For f,g∈ℤ[X] with upper degree bounds m,n (m+n>0), construct
integer U,V with degree(U)<n and degree(V)<m and
f U + g V = Res(f,g;m,n).

The proof identifies the matrix of the bounded-degree Sylvester map
with the Sylvester matrix already defined by the pinned mathlib
v4.24.0, then applies the integral adjugate. It does NOT assume
an integral Bezout certificate.

The nonzero-constant form needs only the explicit nonzero-resultant
premise. The downstream proof must show this from coprimality of A,W
and estimate the determinant by a power of H(F).

## Outstanding

1. Choose t ∈ {0,…,kD} so W_t=Σ t^j F_j is coprime to A over ℚ[X].
2. Derive nonvanishing of the integral Sylvester determinant.
3. Prove |Res(A,W)|≪_{D,k}H(F)^(2D) and the corresponding bound in the
   reciprocal projective chart.
4. Complete the p-adic covering/counting argument of Lemma 4.1.

**Do not report these obligations as done merely because the current
certificate theorem compiles.** No ATH_rev manuscript files are published.

## Effective determinant height (new CI checkpoint)

`SylvesterHeightBound.lean` proves
```math
|\mathrm{Res}(A,W;D,e)| \le (D+e)!\,H^{D+e}
```
for integral A,W with coefficients bounded in modulus by H.

Combining this with `exists_integral_sylvester_certificate`
constructs a nonzero integral Bézout constant K with the same
height bound, **provided** the resultant is nonzero.

When e≤D and H is bounded by a constant times the coefficient
height of F, the exponent is at most 2D. The required bounds on
the selected W_t and nonvanishing of its resultant remain to be
proved from the manuscript hypotheses.
