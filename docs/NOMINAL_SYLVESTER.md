# Exact-left-degree Sylvester determinant

This PR integrates *already validated* PR #5 (integral adjugate
certificates and determinant height) with PR #8 (zero-kernel theorem).
A new theorem seeks to prove that IsCoprime A W over ℂ[X], deg A=D
exactly and deg W<=e imply resultant(A,W;D,e) != 0 even if
the right polynomial loses degree.

This is the missing injectivity-to-determinant link for the
quantitative projective-content Lemma 4.1.

The final proof still needs to pass Lean 4.24.0 CI, with each
declaration included in #print axioms. A valid theorem here does not
construct W from rational gcd-one; see PR #9. It also does not prove
p-adic root-ball counting, divisor loss or the full Lemma 4.1.

No manuscript source is uploaded or published.
