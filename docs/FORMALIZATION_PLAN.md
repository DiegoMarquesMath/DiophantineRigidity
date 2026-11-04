# Formal verification plan — 12 independently reviewable gates

The paper's *exact revised source*, not this plan, is authoritative.

| Gate | Target | Completion condition |
| --- | --- | --- |
| 01 | Source identification and theorem map | Exact source hash and independent statement review |
| 02 | Arithmetic foundations | Heights, primitive factors, contents, rational blocks and integer specialization proved |
| 03 | Finite algebraic type | Uniform jet bounds and analytic/formal equivalence |
| 04 | Local determinant relations (Lemma 3.1) | Correct integral kernel, Taylor exponents and all rank cases |
| 05 | Irreducible Hankel reconstruction (Lemma 3.2) | Quotient field pairing, cofactors and gcd removal |
| 06 | Projective content estimate (Lemma 4.1) | Two p-adic charts, uniform Bezout/content bounds and congruence spacing |
| 07 | Integral resultants (Lemma 4.2) | Sylvester determinant, value bound, constant specialization |
| 08 | Multiscale propagation (Lemma 5.1) | The **same** F, separated nodes, retained density and terminal height |
| 09 | Uniform counting (Lemmas 6.1–6.2; Theorems 1.1, 2.1) | Reducible factors, dyadic blocks and true Q/B uniformity |
| 10 | Metric tail and Cantor (Lemma 7.1; Theorem 1.2) | Every branch Liouville, one K works for all m, images transcendental |
| 11 | Arithmetic descent (Theorem 1.4) | Height boundedness, rational projective line and both directions |
| 12 | Integration / cross-check | Precise corollary route, no custom axioms, full CI and independent statement audit |

A stage is **not** complete merely because its file exists. Every completed
stage needs an actual Lean proof, reproducible build, axiom inspection,
source-to-statement comparison and immutable commit reference.

Section 9 of the manuscript (pointwise threshold) is an optional independent
formalization track and must not be mistaken for the global counting threshold.
