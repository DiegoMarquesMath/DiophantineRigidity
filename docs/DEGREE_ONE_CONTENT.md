# Lemma 4.1: the degree-one congruence argument

The case \(\deg_X F=1\) admits a particularly direct proof avoiding algebraic closures of \(p\)-adic fields. This document records the exact mathematics underlying `LinearChartCongruence.lean`. The full degree-\(D\) lemma is not claimed.

Write
\[
F(X,Y)=\sum_{j=0}^k(a_jX+b_j)Y^j,\qquad a_j,b_j\in\mathbb Z.
\]
For a primitive integral polynomial, \(\gcd(a_0,b_0,\ldots,a_k,b_k)=1\). Hence there are integers \(u_j,v_j\) with
\[
\sum_{j=0}^{k}(u_j a_j+v_j b_j)=1.
\]

For a fixed positive integer \(g\), let \(S_g\) consist of reduced \(p/q\in\mathcal F_Q(E)\) for which
\[
g\mid a_jp+b_jq \quad\text{for all }0\le j\le k.
\]
For two members \(p/q,p'/q'\), put \(\Delta=pq'-p'q\). The exact identities
\[
q'(a_jp+b_jq)-q(a_jp'+b_jq')=a_j\Delta,
\]
\[
p(a_jp'+b_jq')-p'(a_jp+b_jq)=b_j\Delta
\]
show that \(g\mid a_j\Delta\) and \(g\mid b_j\Delta\). Multiplication by the Bézout coefficients and summation gives
\[
\boxed{g\mid\Delta.}
\]
No individual \(a_j\) or \(b_j\) has to be a unit modulo \(g\).

Distinct elements in \(S_g\) therefore satisfy
\[
\left|\frac pq-\frac{p'}{q'}\right|
 =\frac{|\Delta|}{qq'}
 \ge \frac{g}{4Q^2}.
\]
By the already formalized Farey packing theorem,
\[
\boxed{\# S_g\le 1+\frac{4|E|Q^2}{g}.}
\]

For \(\deg_X F=1\), the two-chart Bézout argument supplies a nonzero
integer \(K\), polynomially bounded in the height of \(F\), for which
\(g(p/q)\mid K\). Consequently,
\[
\#\{r\in\mathcal F_Q(E):g(r)>G\}
 \le \sum_{\substack{g\mid K\\g>G}}\#S_g
 \le \tau(|K|)\left(1+\frac{4|E|Q^2}{G}\right).
\]
The standard divisor estimate \(\tau(n)\ll_\epsilon n^\epsilon\),
combined with \(|K|\ll_k H(F)^4\), gives the intended \(D=1\)
case of Lemma 4.1.

## Precise verification boundary

The Lean module proves the two elimination identities, their combination
under a **supplied** integral Bézout certificate, and the fixed-\(g\)
Farey-cardinality bound. The existence of such a certificate from the
global coefficient gcd, the uniform global \(K\), and the final divisor
summation must be checked against the exact theorem interfaces before
claiming the entire \(D=1\) case machine-certified.

For \(D\ge2\), the congruence amplification requires a different argument:
a primitive polynomial of degree \(d\le D\) whose value is divisible
by \(\ell^b\) restricts its arguments to at most \(d\) \(p\)-adic
balls modulo \(\ell^{\lceil b/D\rceil}\). This is the genuinely open
nonarchimedean covering step.
