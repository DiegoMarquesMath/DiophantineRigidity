# Proof-integrity standard

No theorem is marked **fully verified** unless:

1. Its Lean type exactly matches the revised mathematical assertion,
   including quantifier order, ranges, dependencies and endpoint cases.
2. The entire transitive proof compiles using the pinned Lean and mathlib.
3. The theorem has no admitted proof, custom axiom, untrusted oracle, or
   theorem-equivalent assumption introduced merely to close the goal.
4. `#print axioms` is inspected for each main theorem.
5. The source hash, Lean commit SHA, verification command, CI run and
   independent statement review are recorded.

The standard foundations `propext`, `Classical.choice` and `Quot.sound` may
appear in `#print axioms`. That does not authorize additional axioms.

The shell guard is a supplementary source check, not a substitute for the
Lean kernel. A successful build of definitions or imported old results does
not imply the new research theorem.

Run from the project root:

```bash
lake exe cache get
bash scripts/check.sh
```

For direct inspection:

```bash
lake env lean -DwarningAsError=true scripts/Audit.lean
```

Do not claim statement correspondence until the exact local source files
have been compared against the final Lean types.
