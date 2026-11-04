import Mathlib

/-!
# The strict valuation gap in the Lagrange p-adic covering

For D,b≥1 and m=ceil(b/D), a denominator in the
Lagrange interpolation formula is a product of D
differences each having valuation at most m-1.
The key arithmetic inequality is D*(m-1)<b.
This module proves that inequality exactly, including
b=1, D=1 and all nondivisible b, without assumptions
equivalent to the p-adic covering conclusion.

The p-adic valuation estimates of the differences and the
Lagrange polynomial coefficient integrality remain to be
formalized in a separate lemma.
-/

namespace DiophantineRigidity

/-- A positive numerator has positive ceiling quotient by a
positive divisor. -/
theorem ceil_degree_div_pos (D b : ℕ)
    (hD : 0 < D) (hb : 0 < b) :
    0 < b ⌈/⌉ D := by
  by_contra hn
  have hz : b ⌈/⌉ D = 0 := by omega
  have hbound : b ≤ D * (b ⌈/⌉ D) := by
    simpa only [nsmul_eq_mul] using
      (le_smul_ceilDiv (a := D) (b := b) hD)
  rw [hz] at hbound
  omega

/-- For the precise ceiling exponent m=ceil(b/D),
the sum of at most D valuations each bounded by m-1
is strictly smaller than b. -/
theorem degree_mul_ceil_pred_lt
    (D b : ℕ) (hD : 0 < D) (hb : 0 < b) :
    D * ((b ⌈/⌉ D) - 1) < b := by
  have hm : 0 < b ⌈/⌉ D :=
    ceil_degree_div_pos D b hD hb
  by_contra hn
  have hb_le : b ≤ D * ((b ⌈/⌉ D) - 1) := by omega
  have hm_le : b ⌈/⌉ D ≤ (b ⌈/⌉ D) - 1 := by
    exact (ceilDiv_le_iff_le_smul hD).mpr
      (by simpa only [nsmul_eq_mul] using hb_le)
  omega

end DiophantineRigidity
