# Verified status and evidence

This table deliberately distinguishes *source code that compiles* from
*theorems whose exact mathematical claims are proved*.

| Component | Status | Evidence |
| --- | --- | --- |
| Project scaffolding | Verified on main at commit b342c9b | Lean code and automated audit included |
| Polynomial witness definitions | Compiled on main and in the arithmetic-foundations PR | `DiophantineRigidity/Witnesses.lean` |
| Rational spacing / entire-function bridge | Compiled and audited | `DiophantineRigidity/LegacyBridge.lean` |
| New finite-type theorem | Not yet formalized | Gate 03 |
| New local determinant / Hankel recovery | Abstract multiplication pairing proved; reconstruction incomplete | Gates 04–05 |
| New projective content / resultant | Denominator clearing proved; degree-one resultant under CI; general results incomplete | Gates 06–07 |
| New uniform propagation | Exponent identities proved; propagation incomplete | Gate 08 |
| New arbitrary-degree two-height count | Not yet formalized | Gate 09 |
| New all-degree Cantor/S-number theorem | Not yet formalized | Gate 10 |
| New arithmetic descent | Not yet formalized | Gate 11 |
| Full manuscript ↔ Lean certification | Not yet complete | Gate 12 |

The old MahlerLean project has its own validation reports; a proof imported
from that package is not an original new proof in this repository.

Only update a row after a successful Lean build, an axiom audit and an
independent comparison of the exact formal statement with the manuscript.

### Evidence recorded

- [Successful arithmetic/Hankel/exponent audit](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41778705872), source commit `102443a74cea161d3e3237437f512790df876248`.
- Audited declaration axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- `linearResultant_bound` is a later addition and must be validated by its new CI run.
- No new global counting, Cantor/S-number, or descent theorem is yet formalized.
