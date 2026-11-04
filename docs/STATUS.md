# Verified status and evidence

This table deliberately distinguishes *source code that compiles* from
*theorems whose exact mathematical claims are proved*.

| Component | Status | Evidence |
| --- | --- | --- |
| Project scaffolding | Prepared; CI pending first GitHub push | Lean code and automated audit included |
| Polynomial witness definitions | Implemented; compilation still to be run for this independent repository | `DiophantineRigidity/Witnesses.lean` |
| Rational spacing / entire-function bridge | Exact inherited declarations written; CI pending | `DiophantineRigidity/LegacyBridge.lean` |
| New finite-type theorem | Not yet formalized | Gate 03 |
| New local determinant / Hankel recovery | Not yet formalized | Gates 04–05 |
| New projective content / resultant | Not yet formalized | Gates 06–07 |
| New uniform propagation | Not yet formalized | Gate 08 |
| New arbitrary-degree two-height count | Not yet formalized | Gate 09 |
| New all-degree Cantor/S-number theorem | Not yet formalized | Gate 10 |
| New arithmetic descent | Not yet formalized | Gate 11 |
| Full manuscript ↔ Lean certification | Not yet complete | Gate 12 |

The old MahlerLean project has its own validation reports; a proof imported
from that package is not an original new proof in this repository.

Only update a row after a successful Lean build, an axiom audit and an
independent comparison of the exact formal statement with the manuscript.
