# The first nontrivial projective-content bridge

The goal is to close **Lemma 4.1** of the 24-page research manuscript,
not to count compilation progress as mathematical progress.

## Exact proof contracts

Given a finite family A_j, U_j ∈ ℤ[X], upper degree bounds D and E,
and a *supplied* integral Bezout identity

\[
\sum_j U_j A_j = K\in \mathbb Z,
\]

the cleared evaluation identity is

\[
\sum_j q^E U_j(p/q)\,q^D A_j(p/q) = K q^{D+E}.
\]

The content of q^D F(p/q,Y) therefore divides K q^{D+E}.
In the other chart it analogously divides K' p^{D+E'}.
For coprime integer coordinates, a chart-cancellation lemma shows
that the content divides |KK'|.

## Verified vs still to be proved

The module contains proofs of these **conditional** assertions.
No certificate has been constructed here from the gcd hypothesis.

The decisive missing steps are:

1. Choose linear combination W = Σ t^j V_j avoiding all roots of a
   degree-D chart polynomial A (at most kD forbidden t).
2. Implement the integral Sylvester matrix and adjugate, proving an
   identity Σ U_j V_j = K_* ≠ 0 with
   |K_*| ≤ C(D,k) H(F)^(2D) in each chart.
3. Prove the reciprocal-chart coefficient identity and the resulting
   division of the content by K_1 K_2.
4. Formalize the nonarchimedean Gauss-norm root covering, congruence
   separation, and divisor-sum bound. Only then assert the full
   Lemma 4.1 estimate.

This development is checked in a separate PR and must not be described
as the full projective-content lemma until all four obligations pass.
