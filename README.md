# Diophantine Rigidity of Analytic Graphs

[![Lean verification](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/workflows/lean.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-273B5C)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.24.0-485D70)](https://github.com/leanprover-community/mathlib4)

Lean 4 formalization accompanying Diego Marques's manuscript
*Diophantine Rigidity of Analytic Graphs*.

This project develops the arithmetic and analytic infrastructure for a uniform
two-height counting theorem on real-analytic graphs. Its mathematical program
also concerns simultaneous Mahler-exponent bounds on Cantor sets of Liouville
numbers and arithmetic descent.

> **Verification status.** The arithmetic, coprimality, projective-chart,
> and Sylvester-resultant infrastructure contains machine-checked results.
> The **new arbitrary-degree counting theorem, full projective-content
> estimate, multiscale propagation, S-number Cantor theorem, and arithmetic
> descent are not yet proved in Lean**. A successful build certifies the
> declarations that are present, not the outstanding manuscript claims.

## Main mathematical objective

Let $f:I\to\mathbb R$ be real analytic and transcendental over $\mathbb R(X)$,
and let $J\Subset I$. For reduced rational arguments $r=p/q\in J$ with
$Q\le q<2Q$, consider nonzero $P\in\mathbb Z[Y]$ such that

$$
\deg P\le m,\qquad B\le H(P)<2B,\qquad
|P(f(r))|\le L B^{-w}.
$$

The intended theorem gives, uniformly over independent source and polynomial
height scales,

$$
N_{f,m}(Q,B,w)\ll Q^{2-\eta},
\qquad w>2m-1,\quad Q^{u_0}\le B\le Q^U.
$$

The constants must be chosen before $Q$ and $B$. Exact zeros, reducible
witnesses and degree drops are retained.

A further target is one Cantor set $K$ of Liouville numbers in every open
subinterval, with

$$
f(\xi)\text{ transcendental},\qquad
\mu(f(\xi))=2,\qquad
w_m(f(\xi))\le 2m-1\quad(m\ge1)
$$

simultaneously for every $\xi\in K$. **This is not yet a verified theorem
of this new project.**

## Verified supporting results

### Arithmetic foundations

[Witnesses.lean](DiophantineRigidity/Witnesses.lean) defines exact
polynomial small-value witnesses and exceptional rational arguments;
[WitnessMonotonicity.lean](DiophantineRigidity/WitnessMonotonicity.lean)
proves degree monotonicity.
[FareyBounds.lean](DiophantineRigidity/FareyBounds.lean) and
[ArithmeticSpecialization.lean](DiophantineRigidity/ArithmeticSpecialization.lean)
provide rational-block estimates and denominator-cleared specializations.
[IntegerContent.lean](DiophantineRigidity/IntegerContent.lean) develops the
coefficient-gcd interface.

### Projective-chart arithmetic

[BivariateSpecialization.lean](DiophantineRigidity/BivariateSpecialization.lean),
[TwoChartDivisibility.lean](DiophantineRigidity/TwoChartDivisibility.lean),
[ProjectiveBezoutBridge.lean](DiophantineRigidity/ProjectiveBezoutBridge.lean)
and [ProjectiveReciprocity.lean](DiophantineRigidity/ProjectiveReciprocity.lean)
verify exact specialization and reciprocal-chart identities. Under two
supplied integral Bézout certificates they derive

$$
\operatorname{cont}(q^D F(p/q,Y))\mid |K_1K_2|.
$$

The hypotheses on the certificate constants are explicit: this is not the
full uniform $p$-adic counting estimate.

### Polynomial selection and coprimality

[BoundedRootAvoidance.lean](DiophantineRigidity/BoundedRootAvoidance.lean),
[SelectedIntegerCombination.lean](DiophantineRigidity/SelectedIntegerCombination.lean),
[ComplexCoprimality.lean](DiophantineRigidity/ComplexCoprimality.lean), and
[RationalCoefficientCoprimality.lean](DiophantineRigidity/RationalCoefficientCoprimality.lean)
control the choice of an integral auxiliary polynomial

$$
W_t(X)=\sum_{j=0}^{k}t^j V_j(X),\qquad 0\le t\le kD,
$$

including the coefficient-height bound

$$
H(W_t)\le (k+1)(kD+1)^k H
$$

under explicit degree and coefficient-coprimality assumptions.

### Integral Sylvester resultants and effective Bézout certificates

[SylvesterKernel.lean](DiophantineRigidity/SylvesterKernel.lean),
[SylvesterCertificates.lean](DiophantineRigidity/SylvesterCertificates.lean),
[SylvesterHeightBound.lean](DiophantineRigidity/SylvesterHeightBound.lean)
and [ResultantBaseChange.lean](DiophantineRigidity/ResultantBaseChange.lean)
develop the exact-degree Sylvester map, determinant bounds, integer adjugate
certificates, and base change to complex coefficients.

The central recent bridge is
[SelectedResultantBridge.lean](DiophantineRigidity/SelectedResultantBridge.lean).
The declaration
`DiophantineRigidity.exists_selected_bounded_integral_bezout`
constructs $t,U,T,K$, with $K\ne0$, such that

$$
AU+W_tT=K,\qquad
|K|\le (D+e)!\,M^{D+e},
\quad M=\max\{H,(k+1)(kD+1)^kH\}.
$$

This is a quantitative **algebraic ingredient** of Lemma 4.1, not
its final projective-content counting conclusion.

### Independent legacy theorems

[LegacyBridge.lean](DiophantineRigidity/LegacyBridge.lean) imports exact
declarations from the pinned
[MahlerLean](https://github.com/DiegoMarquesMath/MahlerLean) dependency,
including rational spacing and the previously established entire-rigidity
theorem. The earlier degree-one counting and Cantor arguments do **not**
prove the new arbitrary-degree results.

## Manuscript-to-Lean correspondence

| Manuscript component | Current Lean source | Status |
| --- | --- | --- |
| Rational blocks, heights and specialization | `Witnesses`, `FareyBounds`, `ArithmeticSpecialization` | Supporting results verified |
| Lemma 3.1 — local determinant relations | Related legacy infrastructure | Full statement open |
| Lemma 3.2 — Hankel reconstruction | `HankelPairing` | Preliminary results only |
| Lemma 4.1 — projective contents | `ProjectiveBezoutBridge`, `SelectedResultantBridge` | Significant algebraic progress; p-adic estimate open |
| Lemma 4.2 — resultants | `SylvesterCertificates`, `SylvesterHeightBound`, `ResultantBaseChange` | Supporting results verified; final statement comparison pending |
| Lemma 5.1 — multiscale propagation | `PropagationExponents` | Exponent groundwork only |
| Arbitrary-degree two-height counting | No complete declaration | Open |
| Simultaneous Cantor/S-number theorem | No complete declaration | Open |
| Arithmetic descent | No complete declaration | Open |
| Entire-function rigidity via new counting route | `entireRigidityFromLegacy` proves an older route | New derivation open |

Final manuscript-to-Lean comparison requires the exact revised manuscript,
which is deliberately excluded from this public repository.

## Proof architecture

| Step | Role |
| --- | --- |
| Farey bounds and heights | Control rational arguments and independent polynomial heights |
| Finite algebraic type | Provide uniform analytic nondegeneracy |
| Local determinants | Produce integral relations |
| Hankel recovery | Reconstruct a single primitive polynomial |
| Projective contents and resultants | Control arithmetic specializations and coefficient growth |
| Multiscale propagation | Preserve the **same** reconstructed polynomial across scales |
| Two-height counting | Obtain a power saving in the rational count |
| Cantor and S-numbers | Impose every approximation-degree constraint on one set |
| Arithmetic descent | Recover rational defining equations from dense specializations |

See the [twelve-gate plan](docs/FORMALIZATION_PLAN.md),
[statement contracts](docs/PROOF_CONTRACTS.md), and
[verification policy](docs/VERIFICATION.md).

## Verification

The development pins **Lean 4.24.0**, **mathlib v4.24.0**, and a fixed
revision of MahlerLean. Reproduce the current published proofs with

~~~bash
git clone https://github.com/DiegoMarquesMath/DiophantineRigidity.git
cd DiophantineRigidity
lake exe cache get
bash scripts/check.sh
~~~

The script builds the library, checks project modules with warnings as
errors, audits principal declarations with `#print axioms` and rejects
`sorryAx` and nonstandard research axioms. Only the standard logical
foundations `propext`, `Classical.choice` and `Quot.sound` are allowed.

**Verified proof checkpoint:** commit
[`5e563e74d0cf8aa72913cf918faf006e1ef41df5`](https://github.com/DiegoMarquesMath/DiophantineRigidity/tree/5e563e74d0cf8aa72913cf918faf006e1ef41df5);
[GitHub Actions run 41879338537 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41879338537).

The checkpoint certifies the exact Lean declarations in that commit,
**not** the research theorems listed above as open. Read
[VALIDATION.md](VALIDATION.md) for verification scope and provenance.

## Repository structure

| Path | Purpose |
| --- | --- |
| [DiophantineRigidity/](DiophantineRigidity/) | Lean source modules |
| [scripts/check.sh](scripts/check.sh) | Reproducible build and axiom check |
| [scripts/Audit.lean](scripts/Audit.lean) | Audited theorem declarations |
| [VALIDATION.md](VALIDATION.md) | Immutable CI evidence and limitations |
| [docs/STATUS.md](docs/STATUS.md) | Precisely scoped completed, partial and open obligations |
| [docs/FORMALIZATION_PLAN.md](docs/FORMALIZATION_PLAN.md) | Twelve reviewable proof gates |
| [docs/INTEGRATION_2026-11-04.md](docs/INTEGRATION_2026-11-04.md) | Source-commit provenance |
| [docs/SELECTED_RESULTANT_BEZOUT.md](docs/SELECTED_RESULTANT_BEZOUT.md) | Constructive quantitative Bézout interface |
| [AGENTS.md](AGENTS.md) | Proof-integrity instructions for agents |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution standards |

## Open mathematical obligations

The immediate priority is completing **Lemma 4.1**, including uniform
$p$-adic root coverings, congruence separation and divisor sums.
Finite algebraic type, determinant relations, Hankel reconstruction and
same-polynomial multiscale propagation remain indispensable for the
new counting theorem and its corollaries.

## Citation and scope

Cite an **exact verified commit**, not only a moving branch badge.
The repository's [CITATION.cff](CITATION.cff) supplies software metadata;
cite the mathematical manuscript separately.

Maintained by [Diego Marques](https://github.com/DiegoMarquesMath),
Department of Mathematics, Universidade de Brasília.
