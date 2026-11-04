# Sylvester kernel rigidity — new proof target

The selected integer polynomial from the verified PR #7 is coprime
to A over ℂ[X]. The main new assertion is a zero-kernel theorem:

If A≠0, natDegree(A)=D and IsCoprime A W, then
AU+WV=0 together with degree(V)<D forces U=V=0.

The theorem is applied to one W_t chosen with t≤kD and is
precisely the arithmetic-to-linear-algebra bridge that will
be used for the nonzero Sylvester determinant.

The matrix/determinant identification is still needed to conclude
Res(A,W_t;D,e)≠0 at nominal degrees. This remains distinct from
the new assertion until independently Lean-verified.

No manuscript source is published. CI/axiom audit pending.
