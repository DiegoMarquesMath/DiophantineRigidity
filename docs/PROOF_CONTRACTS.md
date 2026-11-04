# Proof contracts and mathematical boundaries

These are provisional until compared against the author's exact `ATH_rev.tex`.
They describe the intended mathematics; **they are not established theorems**.

## Source fractions and height

For each denominator block, use canonical reduced rationals $r=p/q$ with
$Q\le q<2Q$ and $r\in J$. Integer polynomial witnesses $P\neq0$ satisfy
$\deg P\le m$, $B\le H(P)<2B$ and
$|P(f(r))|\le L B^{-w}$. Exact zeros and nonprimitive polynomials count.
The set counts rational **arguments**, not witness pairs.

## Quantifier order in the main theorem

For fixed transcendental analytic $f$, compact $J$, $m\ge1$,
$w>2m-1$, $0<u_0\le U$ and $L>0$, choose $\eta,C,Q_0$ before
$Q\ge Q_0$ and $Q^{u_0}\le B\le Q^U$. For families, the constants
must be independent of the member of the family under **common** finite-type
and derivative bounds.

## Central estimates

- Lemma 3.1: a *nonzero integral relation* for every admissible row; include
  rank zero and fewer-than-full-row cases.
- Lemma 3.2: one primitive $F\in\mathbb Z[X,Y]$, coprime coefficient
  polynomials in $X$, specialization proportional to each retained irreducible
  witness; control degree and height.
- Lemma 4.1: the projective-content estimate must be **uniform in F**, and
  use both $p$-adic charts; treat $D=0$ separately.
- Lemma 4.2: integral resultant and the precise powers of both polynomial
  heights; include constant specializations.
- Lemma 5.1: preserve exact proportionality to original witnesses after
  each expansion, and never accumulate interpolated error exponents.

## Main consequences

- The Cantor theorem must impose all $w_m$ bounds on one set, for **every**
  point of that set. Exclude algebraic images separately, not merely by $w_1$.
- Arithmetic descent requires more than projective convergence:
  positive density plus content estimates force the integer height to remain
  bounded, and hence yield rationality of the defining equation.
- The entire-function statement imported from MahlerLean is **already
  available through an earlier proof** but its deduction through the new
  stronger theorem is a separate target.

## Edge cases to test

$m=1$; $D=0$; degree drops; exact zeros; repeated factors; small
irreducible-factor heights; nonreal algebraic approximants where allowed;
translates of $f$; dyadic height endpoints; arbitrarily large Q; all
branches and all approximation degrees simultaneously.
