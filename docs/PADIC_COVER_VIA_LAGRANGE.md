# Projective-content Lemma 4.1: an arithmetic route to the p-adic cover

The current manuscript proves the p-adic root covering by factoring the
coefficient polynomials over an algebraic closure of \(\mathbb Q_\ell\).
For formalization, the following entirely **rational Lagrange-interpolation**
argument avoids roots in any algebraically closed valued field.

## The local covering proposition

Fix a prime \(\ell\), integers \(D,b\ge1\), and set
\(m=\lceil b/D\rceil\).
Suppose
\[
V(X)=\sum_{j=0}^D c_jX^j\in\mathbb Z_\ell[X],
\quad \min_jv_\ell(c_j)=0.
\]
For \(z\in\mathbb Z_\ell\), let \(\mathscr S\) be the set of solutions of
\(v_\ell(V(z))\ge b\).
**Claim:** the reduction of \(\mathscr S\) modulo \(\ell^m\) has
cardinality at most \(D\).

### Proof

Suppose that \(z_0,\ldots,z_D\in\mathscr S\) lie in distinct residue
classes modulo \(\ell^m\). Then for \(i\ne j\),
\[
v_\ell(z_i-z_j)\le m-1.
\]
As \(\deg V\le D\), Lagrange interpolation gives the polynomial identity
\[
V(X)=\sum_{i=0}^D
 V(z_i)
 \frac{\prod_{j\ne i}(X-z_j)}
      {\prod_{j\ne i}(z_i-z_j)}
\quad\text{in }\mathbb Q_\ell[X].
\]
For every \(i\),
\[
v_\ell\left(\prod_{j\ne i}(z_i-z_j)\right)
\le D(m-1)<b.
\]
All coefficients of \(\prod_{j\ne i}(X-z_j)\) belong to
\(\mathbb Z_\ell\). Because \(v_\ell(V(z_i))\ge b\), every coefficient
of the \(i\)-th summand is divisible by \(\ell\). Thus all coefficients
of \(V\) are divisible by \(\ell\), contradicting its normalized Gauss
norm. Hence at most \(D\) residue classes occur. \(\square\)

The strict inequality uses the definition of the ceiling:
\(m-1<b/D\). No Hensel simplicity or discriminant assumption is needed,
and repeated roots are included.

## Translation to projective rational arguments

For a reduced rational \(p/q\), choose the chart where the denominator
is an \(\ell\)-adic unit. In the first chart use \(p/q\) when
\(\ell\nmid q\); otherwise use \(q/p\). The rational is \(\ell\)-integral
in the chosen chart. Global primitivity of \(F\) means that in each
projective chart some coefficient polynomial has an \(\ell\)-adic unit
coefficient. The proposition then supplies at most \(D\) residue
classes in either chart, hence at most \(2D\) chart-and-class choices.

If two arguments use the same chart and residue class, their coordinate
difference is divisible by \(\ell^m\) in \(\mathbb Z_\ell\).
Since both chart denominators are units,
\[
\ell^m\mid pq'-p'q.
\]
For a prescribed \(g=\prod_{\ell}\ell^{b_\ell}\), multiplying these
congruences over distinct primes yields a modulus
\[
M=\prod_{\ell\mid g}\ell^{\lceil b_\ell/D\rceil}
 \ge g^{1/D}.
\]

The already verified Lean modules
`CongruenceSpacing.lean` and `ModularFareyPacking.lean` then give
\[
\#S_g\le (2D)^{\omega(g)}
       \left(1+\frac{4|E|Q^2}{g^{1/D}}\right).
\]

## Remaining Lean obligations

1. Formalize the exact Lagrange-interpolation coefficient identity
   over \(\mathbb Q_\ell\) using
   `Mathlib/LinearAlgebra/Lagrange.lean`.
2. Formalize valuations of the interpolation denominators and the
   coefficient-unit contradiction.
3. Implement the chart selection and extraction of residue classes;
   prove they induce the required cross-determinant congruences.
4. Construct the finite product modulus and its \(g^{1/D}\) lower bound.
5. Prove the uniform weighted divisor estimate
   \[
     \sum_{g\mid K}(2D)^{\omega(g)}
       \ll_{D,\varepsilon} K^\varepsilon.
   \]
6. Combine with the bounded integer Bézout constants previously
   constructed in `SelectedResultantBridge.lean` for each chart.

**Status:** this is a complete *mathematical proof* of the local
covering proposition, not a claim that it has yet been kernel-checked
in Lean. Its existence, rather than an assumed p-adic root-covering
hypothesis, is the next formalization target.
