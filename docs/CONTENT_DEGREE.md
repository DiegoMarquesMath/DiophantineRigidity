# Content and degree invariants

This focused branch extends the **successfully verified** arithmetic
foundations at `b3e0d8a823123869743ce2028b8360137da2b393`.

New goals (CI status pending):
- `integerContent_eq_zero_iff`: gcd of coefficients vanishes exactly
  when the integer polynomial vanishes.
- `integerContent_pos_of_ne_zero`: positive content of a nonzero polynomial.
- `clearedBivariate_degree_le`: the specialization in X cannot increase
  the degree in Y, including degree drops.
- `clearedBivariate_natDegree_le`: natural-degree version of the bound.

These lemmas address boundary cases in Lemmas 4.1 and 5.1; they are not
the arbitrary-degree content count, nor the propagation theorem.

No revised manuscript source has been published.
