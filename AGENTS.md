# Research agent protocol — DiophantineRigidity

## Mission

Formalize the revised paper *Diophantine Rigidity of Analytic Graphs* in
Lean 4 with the exact parameters, quantifiers and proof dependencies.
The paper is locally available as `paper/ATH_rev.tex`; it is ignored by Git.

## Proof integrity (non-negotiable)

- No `sorry`, `admit`, untrusted axioms, opaque proof-oracles or theorem-equivalent assumptions.
- Never weaken theorem conclusions or insert genericity or extra smoothness hypotheses.
- Do not silently replace real-scale Q by a natural-scale Q unless equivalence is proved.
- Do not throw away exact zeros, factors, repeated factors or specialized degree drops.
- Uniform constants in the main count must be selected *before* Q and B.
- Preserve the **same** reconstructed F through propagation. Repeatedly interpolating with accumulated losses is not the stated proof.
- Separate code compilation from full statement fidelity and axiom certification.
- The original MahlerLean code is an external, pinned dependency: never present its degree-one results as the new arbitrary-degree theorem.
- Do not publish unpublished paper, local statement audits, or internal notes without author authorization.

## Procedure for each mathematical result

1. Record the exact TeX lemma and a minimal Lean interface in `docs/local/`.
2. Use `#check` to inspect precise types of candidate mathlib/legacy lemmas.
3. Prove small independent lemmas and check them before continuing.
4. Run `bash scripts/check.sh` once per meaningful checkpoint, avoiding duplicate parallel builds.
5. Extend `scripts/Audit.lean`, inspect its axiom output and compare theorem types to paper.
6. Update public `docs/STATUS.md` only with evidence supported by a successful verification.
7. Create small focused commits, with no auto merge and no claims of completion for unproved results.
8. On a blocker, report the exact mathematical obligation rather than altering the theorem.

## Priority order

See `docs/FORMALIZATION_PLAN.md`. Projective content, uniform multiscale
propagation and simultaneous measure-positive Cantor induction are the highest-risk steps.
