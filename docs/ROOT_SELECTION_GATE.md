# Critical root-selection bridge

This change replaces the finite set of points in the bounded-avoidance
lemma by the **actual complex roots** of an integer coefficient
polynomial, embedded in ℂ[X].

The declared result selects t∈ℕ with t≤kD and an actual W_t∈ℤ[X]
such that W_t is nonzero at every root of A, with coefficient bound
H(W_t)≤(k+1)(kD+1)^k H.

Still not proved: the no-common-zero hypothesis from coprimality in
ℚ[X], a nonzero integer Sylvester resultant for W_t, the two-chart
quantitative certificate and the p-adic content-counting estimate.

The new source must pass CI and #print axioms before certification.
