# Reuse from MahlerLean without conflating research results

This project is **a separate Git repository**. The earlier repo is pinned
as a Lake dependency; nothing is copied from its Git history.

| Earlier module | Candidate reusable fact | Still required here |
| --- | --- | --- |
| `MahlerLean/RationalBlocks.lean` | Exact reduced rational blocks | Polynomial height B and arbitrary-degree witnesses |
| `MahlerLean/FareySeparation.lean` | Rational spacing and packing | Stronger content-dependent congruence spacing |
| `MahlerLean/FareyCounting.lean`, `TotientBlock.lean` | Interval counts and supply | Higher-degree witness decomposition |
| `MahlerLean/FiniteJetCover.lean` | Finite compact jet covers | Real polynomial-in-Y finite algebraic type |
| `MahlerLean/DeterminantRelations.lean` | Determinant templates | Shifted witnesses up to degree 2k-1 |
| `MahlerLean/CurveTaylorBounds.lean` | Taylor estimates | Uniform Lagrange interpolation for F(X,T_s(X)) |
| `MahlerLean/CantorTree.lean`, `CantorTopology.lean` | Binary topology and shrinking intervals | Positive-measure children and all-degree conditions |
| `MahlerLean/EntireRigidity.lean` | Existing entire-function conclusion | New dependency route from S-number images |

The historical `MahlerLean.proposition_5_1` treats *rational targets* and
has bounds different from the new $w>2m-1$ theorem. Reusing it as a proof
of the new arbitrary-degree result would be mathematically invalid.

Pinned source commit: `5a91bd60ebb8200886bdca21cc9c178bfb1f5f1d`.
