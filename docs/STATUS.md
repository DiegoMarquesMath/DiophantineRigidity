# Status of formal verification — 2026-11-04

**Current main-branch checkpoint:** [`b3ceac232494`](https://github.com/DiegoMarquesMath/DiophantineRigidity/commit/b3ceac232494702aa1e818c8c13198c6266e2200), [CI successful](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41886957638). This includes the integrated algebraic source and the selected bounded nonzero integral Bézout certificate; it does not prove the full manuscript Lemma 4.1. See [VALIDATION.md](../VALIDATION.md).


> **Scope:** This status concerns the new manuscript *Diophantine Rigidity of Analytic Graphs*, not the already existing MahlerLean theorem in isolation. **No new global counting, simultaneous S-number or arithmetic descent theorem is certified yet.**

## Evidence hierarchy

1. **Certified code at a fixed commit:** exact Lean declarations checked by successful GitHub Actions and explicit `#print axioms` output.
2. **Integrated code:** source present on `main`, with successful combined CI at the exact checkpoint above. This alone does not establish manuscript-to-Lean statement equivalence.
3. **Partial manuscript lemma:** genuine machine-checked supporting statements, but the full source-level lemma is not yet proved.
4. **Open:** no completed exact Lean proof of the manuscript claim.
5. **Local/unpublished:** described in prior work but not accessible here as committed source; must not be claimed verified.

## Gates and precise status

| Gate | Research obligation | Status | Available evidence / missing work |
|---|---|---|---|
| 01 | Source locking and theorem map | **Partial** | Repository proof contracts available; exact `paper/ATH_rev.tex` remains local and is not public |
| 02 | Heights, primitive factors, Farey blocks, specializations | **Substantial partial** | `FareyBounds`, `ArithmeticSpecialization`, `IntegerContent`, `BivariateSpecialization`, `Witnesses`; global source fidelity still outstanding |
| 03 | Finite algebraic type and uniform jet bounds | **Open** | Related legacy analytic modules exist; no exact new FT theorem certified |
| 04 | Local integral determinant relations (Lemma 3.1) | **Open** | Legacy determinant tools are reusable, not the new complete statement |
| 05 | Hankel reconstruction (Lemma 3.2) | **Partial** | `HankelPairing` only; common primitive reconstructing polynomial still missing |
| 06 | Projective p-adic contents (Lemma 4.1) | **Significant partial** | Two-chart divisibility, reflection, bounded root avoidance, selected integral combinations, coefficient coprimality and bounded nonzero integral Bézout certificates proved; **full uniform content bound unproved** |
| 07 | Integral resultant estimate (Lemma 4.2) | **Significant partial** | Sylvester kernel, certificates, height bounds, nominal-degree nonvanishing, base change; full manuscript comparison incomplete |
| 08 | Same-polynomial multiscale propagation (Lemma 5.1) | **Open** | Exponent identities only; the global persistence and density proof is missing |
| 09 | Arbitrary-degree two-height counting | **Open** | No theorem `N ≪ Q^(2−η)` for all m with two independent heights |
| 10 | Simultaneous all-degree Cantor / S-number images | **Open** | Legacy `MahlerLean` Cantor proof does not imply this new claim |
| 11 | Arithmetic descent | **Open** | Positive-density specialization to rational defining equation remains to prove |
| 12 | Full manuscript-to-Lean audit | **Open** | Need exact source mapping, all main declarations, transitive axiom and CI certification |

**No full manuscript gate is recorded as complete.** Many genuine supporting theorems are formalized, integrated on `main` and CI-validated; each gate requires additional exact-statement review.

## Previously validated source commits

| Source | Commit | CI |
|---|---|---|
| Accumulated arithmetic / root avoidance / Sylvester kernel and nominal-degree resultant, [PR #10](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/10) | `84f8fc5041899d20a7e9aa8f588d808e881e1f1d` | [success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41851694299) |
| Rational coefficient coprimality, [PR #9](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/9) | `1738c9db83820b1c19a9913cffcc9a2867e5f402` | [success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41850220738) |
| Resultant base change, [PR #11](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/11) | `6e6dd5e7487e7971f0f5c1646f0eb33f143910ce` | [success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41852264160) |
| Degree monotonicity, [PR #12](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/12) | `0a6d19bd302241a8c7b6b089db70c173d9e6fc57` | [success](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41862008608) |

These runs certify their respective commits. The recovered modules have now also been integrated into `main`: [PR #13](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/13) and [PR #14](https://github.com/DiegoMarquesMath/DiophantineRigidity/pull/14) were merged, and the combined `main` passed [CI run 41886957638](https://github.com/DiegoMarquesMath/DiophantineRigidity/actions/runs/41886957638).

## Priority now

1. Preserve successful integrated CI checkpoints and review exact theorem types against the revised manuscript.
2. Compare the exact revised manuscript Lemmas 3.1, 3.2, 4.1, 4.2 and 5.1 with Lean interfaces.
3. Complete the uniform polynomial-selection / projective-content argument, including p-adic covers and divisor sums, without inserting theorem-equivalent hypotheses.
4. Prove multiscale propagation of one fixed reconstructed polynomial; then the counting theorem, simultaneous Cantor theorem and arithmetic descent.
5. For future proof changes, require a successful CI run, axiom audit and exact-statement comparison before claiming a manuscript lemma complete.

**Local-only work:** the Mac folder `~/Developer/MahlerLeanATH` and any uncommitted results cannot be inspected from GitHub. There is no truthful way to declare those files incorporated until their bytes are supplied or published.
