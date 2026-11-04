# Lemma 4.1 — selection to quantitative integral Bézout

## Integrated Lean results

The file `DiophantineRigidity/SelectedResultantBridge.lean` composes the existing
finite root-avoidance, rational coefficient coprimality, exact-degree Sylvester
nonvanishing, base change to integers, and adjugate certificate results.

For `A, V₀, ..., Vₖ ∈ ℤ[X]`, assume the rational coefficient polynomials
generate the unit ideal, `A ≠ 0` with exact complex degree `D`,
`deg Vⱼ ≤ e`, and each integer coefficient of `A` and `Vⱼ` has
modulus at most `H ≥ 0`. Let

```
W_t(X) = Σ_{j=0}^k t^j V_j(X),
M = max(H, (k+1)(kD+1)^k H).
```

The newly composed theorem aims to supply an integer `0 ≤ t ≤ kD`,
integer polynomials `U,T`, and a **nonzero** integer `K` with

```
A U + W_t T = K,
|K| ≤ (D+e)! M^(D+e),
deg U < e, deg T < D.
```

There is no hypothesis assuming a selected resultant or a Bézout certificate.
The nonzero resultant is derived from coprimality (through the pinned
complex-polynomial criterion), then the certificate is constructed by
the integer Sylvester adjugate.

**Certification:** check the CI job at the exact head commit and inspect
`scripts/Audit.lean`. Until green CI, these are proof candidates, not
certified statements.

## Remaining gap to the *full* Lemma 4.1

1. Compare the input unit-ideal condition and exact-degree conventions with
   the revised TeX; handle any exceptional zero/constant cases explicitly.
2. Apply this bounded certificate to each reciprocal projective chart,
   retaining an explicit uniform bound on the two constants.
3. Build the nonarchimedean Gauss-root covering, congruence spacing and
   divisor-sum estimate with exact dependence on height, degree and scale.
4. Derive the **uniform projective-content counting assertion**, rather than
   stopping at divisibility by a bounded nonzero integer.

This documentation deliberately distinguishes algebraic certificate
construction from the still-open quantitative counting estimate.
