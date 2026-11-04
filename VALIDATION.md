# Verification record

This document records evidence for **actual Lean declarations**, not for
unformalized manuscript assertions. The project uses Lean **4.24.0**,
mathlib **v4.24.0** and a pinned dependency on MahlerLean.

## Most recent successful research-code checkpoint

- **Source commit:** [`5e563e74d0cf8aa72913cf918faf006e1ef41df5`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/5e563e74d0cf8aa72913cf918faf006e1ef41df5)
- **GitHub Actions:** [run 41879338537 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41879338537)
- **Command:** `bash scripts/check.sh`, as configured in the checked commit.
- **Scope:** rational and polynomial arithmetic, Bézout chart identities, polynomial combination/complex coprimality, Sylvester resultants and bounded integral Bézout selection.
- **Proof audit:** `scripts/Audit.lean` runs `#print axioms` on the named declarations and the check script rejects `sorryAx` or any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

This checkpoint includes the constructive theorem
`DiophantineRigidity.exists_selected_bounded_integral_bezout` in
[SelectedResultantBridge.lean](DiophantineRigidity/SelectedResultantBridge.lean).

## Earlier successful checkpoints

| Area | Source commit | GitHub Actions |
| --- | --- | --- |
| Consolidated Lean branch | [`a4923a2133`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/a4923a2133e278db250ff99261aa0766ffdc5a0f) | [41869914411 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41869914411) |
| Selected nonzero integral resultant | [`6fdd7d9d5a`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/6fdd7d9d5a684d6f35dce3c03025968bce65478b) | [41878409090 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41878409090) |
| Nominal-degree Sylvester resultant | [`84f8fc5041`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/84f8fc5041899d20a7e9aa8f588d808e881e1f1d) | [41851694299 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41851694299) |
| Coprimality over rational polynomials | [`1738c9db83`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/1738c9db83820b1c19a9913cffcc9a2867e5f402) | [41850220738 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41850220738) |
| Integral-to-complex resultant base change | [`6e6dd5e748`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/6e6dd5e7487e7971f0f5c1646f0eb33f143910ce) | [41852264160 — success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41852264160) |

## What these checks do not establish

A successfully checked algebraic lemma is not automatically equivalent
to the corresponding result in the revised paper. In particular,
these runs **do not certify** the full projective-content estimate,
local determinant or Hankel reconstruction lemmas, same-polynomial
propagation, arbitrary-degree two-height counting, simultaneous
S-number Cantor theorem, or arithmetic descent.

Manuscript-to-Lean fidelity requires independent comparison of
the exact TeX statements, including uniform constants, quantifier order,
endpoints, factors, repeated roots and degree drops. The revised
manuscript is not committed to the public repository.

## Reproducing the current state

~~~bash
git clone https://github.com/DiegoMarquesMath/DiophantineRigidity.git
cd DiophantineRigidity
lake exe cache get
bash scripts/check.sh
~~~

For reproducibility of a publication claim, check out the **exact
committed SHA** first, not merely the moving `main` branch. After a
new integration or documentation commit, inspect its own CI result;
a green run from an earlier commit never certifies later source changes.
