# Lemma 4.1 — independent proof audit and Lean proof obligations

**Source:** *Diophantine Rigidity of Analytic Graphs*, Section 4, Lemma 4.1 (24-page manuscript, revision of 2026-11-04).

**Important distinction:** The proof below is a *mathematical* proof with its quantifiers and boundary cases exposed. It does **not** assert that the four remaining arguments have all been kernel-certified in Lean. Never mark Lemma 4.1 verified until a single Lean theorem of this exact strength has a green build and a statement comparison.

## Exact assertion

Let
\[
F(X,Y)=\sum_{j=0}^{k}F_j(X)Y^j\in\mathbb Z[X,Y]
\]
be primitive over \(\mathbb Z\), with \(\gcd_jF_j=1\) in \(\mathbb Q[X]\). Put \(D=\deg_XF\), \(H=\max(2,H(F))\), and for reduced \(p/q\) with \(q>0\) define
\[
A_j(p,q)=q^D F_j(p/q)\in\mathbb Z,\qquad
g(p/q)=\gcd_{0\le j\le k}|A_j(p,q)|.
\]
For \(D=0\), \(g(p/q)=1\). For \(D\ge1\), any interval \(E\), \(G\ge1\), \(\zeta>0\), and denominator block \(Q\le q<2Q\),
\[
\#\{r\in\mathcal F_Q(E):g(r)>G\}
\le C_{D,k,\zeta}\,H^\zeta
\bigl(1+|E|Q^2G^{-1/D}\bigr).
\]
The constant is independent of \(Q,G,E\) and the coefficients of \(F\) after the displayed height factor. Count each reduced rational argument once.

## A. Uniform certificate for two projective charts

Form homogeneous degree-\(D\) coefficient forms \(A_j(S,T)=T^DF_j(S/T)\).
They have no common zero in \(\mathbf P^1(\mathbb C)\): a finite common zero contradicts the rational coefficient gcd, and a common zero at infinity would mean that no coefficient polynomial has degree \(D\). The forms have coefficients with maximum absolute value at most \(H\).

In the chart \(T=1\), pick one coefficient polynomial \(A\) of exact degree \(D\). Since its roots have no common zero with the coefficient family, the standard bounded integer selection argument finds \(0\le t\le kD\) such that \(W_t=\sum_{j=0}^kt^jF_j\) is coprime to \(A\); its height is \(O_{D,k}(H)\). Integral Sylvester adjugates give an identity
\[
U A+V W_t=K_1,\qquad
0<|K_1|\le C_{D,k}H^{2D}.
\]
Repeat with the reflected coefficient polynomials \(A_j(1,Z)\) to obtain \(K_2\) of the same type. For primitive \((p,q)\) with \(pq\ne0\), clearing denominators in the two identities gives
\[
g(p/q)\mid K_1q^{D+e_1},\quad
g(p/q)\mid K_2p^{D+e_2},
\]
so \(\gcd(p,q)=1\) implies
\[
g(p/q)\mid K:=|K_1K_2|,\qquad
0<K\le C_{D,k}H^{4D}.
\]
The reduced fraction \(0/1\) can be handled separately (at most one argument), so the \(p=0\) case is not silently discarded.

The project already verifies significant ingredients in
`SelectedResultantBridge.lean`,
`ProjectiveReciprocity.lean` and
`ProjectiveBezoutBridge.lean`. Exact source-to-Lean correspondence and the constructive assembly of both certificates into one final theorem are still review obligations.

## B. The p-adic covering via Lagrange interpolation (no algebraic closure)

Fix a prime \(\ell\), \(D\ge1\), \(b\ge1\), and put \(m=\lceil b/D\rceil\).
Let \(V\in\mathbb Z_\ell[X]\) have degree \(\le D\) and at least one unit coefficient. Then the set
\[
\mathcal R=\{z\in\mathbb Z_\ell:V(z)\in\ell^b\mathbb Z_\ell\}
\]
meets **at most \(D\)** residue classes modulo \(\ell^m\).

Suppose otherwise. Choose \(D+1\) points \(z_0,\ldots,z_D\in\mathcal R\) representing distinct classes mod \(\ell^m\). Thus for every \(i\ne j\),
\[
v_\ell(z_i-z_j)\le m-1.
\]
Lagrange interpolation in \(\mathbb Q_\ell[X]\) (valid for polynomials of degree \(\le D\)) yields
\[
V(X)=\sum_{i=0}^D V(z_i)
\frac{\prod_{j\ne i}(X-z_j)}
{\prod_{j\ne i}(z_i-z_j)}.
\]
The numerator polynomial \(\prod_{j\ne i}(X-z_j)\) has integral coefficients. Its scalar multiplier has valuation at least
\[
b-\sum_{j\ne i}v_\ell(z_i-z_j)
\ge b-D(m-1)>0,
\]
because \(m=\lceil b/D\rceil\) implies \(D(m-1)<b\).
Every coefficient of every summand lies in \(\ell\mathbb Z_\ell\), hence every coefficient of \(V\) lies in that maximal ideal: contradiction. Repeated roots and non-squarefree reductions are allowed.

**Lean implementation contract:** certify this statement in a suitable local valued field/ring, rather than postulating the existence of a bounded set of residue classes. Mathlib includes `Lagrange.eq_interpolate`, `PadicInt`, `PadicAlgCl`, and `ZMod`. The special case \(m=1\) has already been verified as `prime_residue_root_classes_card_le`; it is **not** the general theorem.

## C. Two charts and composite modulus

For each prime power \(\ell^b\Vert g(p/q)\), choose the chart whose denominator is an \(\ell\)-adic unit:
\[
z=p/q\quad\text{if }\ell\nmid q,\qquad
z=q/p\quad\text{if }\ell\mid q.
\]
The second chart is legitimate because \(\gcd(p,q)=1\).
In either chart, all coefficient polynomials vanish modulo \(\ell^b\) at \(z\).
Primitivity over \(\mathbb Z\) guarantees that **at least one** of these coefficient polynomials has a unit coefficient modulo \(\ell\). It can depend on \(\ell\), but not on \(p/q\). By B, at most \(D\) residue classes in each chart occur, so at most \(2D\) chart-and-residue choices per prime.

Two fractions with the same choices for a fixed \(\ell\) have equal affine coordinates modulo \(\ell^m\). In the chosen chart both denominators are units, so
\[
\ell^m\mid pq'-p'q.
\]
For a fixed divisor \(g=\prod_{\ell}\ell^{b_\ell}\) of \(K\), partition the corresponding rational arguments into at most \((2D)^{\omega(g)}\) classes. Within each class the Chinese remainder theorem gives
\[
M_g:=\prod_{\ell\mid g}\ell^{\lceil b_\ell/D\rceil}
\mid pq'-p'q,\qquad
M_g^D\ge g.
\]
The second inequality is now separately certified in
`PrimePowerModulusGrowth.lean`; `TwoChartModularCoordinate.lean` (subject to its own CI) establishes the coordinate-to-cross-determinant algebra for each chart. The class-producing map is still not fully formalized.

## D. Packing and divisor summation

If distinct reduced fractions with \(Q\le q,q'<2Q\) have \(M_g\mid pq'-p'q\), then
\[
|p/q-p'/q'|=\frac{|pq'-p'q|}{qq'}\ge \frac{M_g}{4Q^2}.
\]
Any interval \(E\) therefore contains at most
\(1+4|E|Q^2/M_g\) members of one class. Hence for fixed \(g\mid K\),
\[
\#\{r\in\mathcal F_Q(E):g(r)=g\}
\le (2D)^{\omega(g)}
(1+4|E|Q^2g^{-1/D}).
\]
Sum over \(g\mid K\), \(g>G\):
\[
\#\{r:g(r)>G\}
\le \Bigl(1+4|E|Q^2G^{-1/D}\Bigr)
\sum_{g\mid K}(2D)^{\omega(g)}.
\]
Because \(\omega(g)\le\omega(K)\) for \(g\mid K\),
\[
\sum_{g\mid K}(2D)^{\omega(g)}
\le \tau(K)(2D)^{\omega(K)}
\ll_{D,\varepsilon}K^\varepsilon.
\]
Here the last inequality is the standard **weighted divisor bound**, requiring its own formal proof. One elementary proof uses the prime factorization \(K=\prod_p p^{a_p}\) and
\[
\tau(K)(2D)^{\omega(K)}=\prod_{p\mid K}(a_p+1)(2D).
\]
For every \(\varepsilon>0\) one can choose \(P_0\) so that
\((a+1)2D\le p^{a\varepsilon}\) for every \(p\ge P_0\) and \(a\ge1\).
For each of the finitely many smaller primes \(p<P_0\), the ratio
\((a+1)2D/p^{a\varepsilon}\) is uniformly bounded over \(a\ge1\).
Multiplication yields a constant depending only on \(D,\varepsilon\).

Finally set \(\varepsilon=\zeta/(4D)\) and use \(K\le C_{D,k}H^{4D}\).
The contribution of \(0/1\), if present, is absorbed by the additive term.

## Exact status of the four obligations

| Obligation | Mathematical proof | New complete Lean theorem |
| --- | --- | --- |
| Full \(\ell^b\) covering | Written above | **Pending**: valuations and Lagrange denominators |
| Projective class map and \(M_g\) | Written above; numeric \(M_g^D\ge g\) already in Lean | **Partial**: coordinate congruence certified separately after CI; class map pending |
| Weighted divisor bound | Written above | **Partial**: exact finite inequality in PR #23; \(\varepsilon\)-bound pending |
| Full Lemma 4.1 assembly | Written above | **Pending**: must consume complete proofs from previous rows |

Do not use hypotheses of the form “assume the required covering bound”
or “assume the final weighted sum bound” to certify the final theorem;
those are precisely the missing claims.
