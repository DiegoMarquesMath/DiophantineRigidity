import Mathlib.Data.ZMod.Basic

/-!
# Reciprocal projective congruences

For a residue class z modulo M, the equations p=z*q and q=z*p
provide the two standard projective affine charts. Every pair
of points with the same coordinate in the *same chart* has a
cross determinant divisible by M. No division is required in
ZMod M, so the lemmas work for nonprime composite moduli and
are valid for arbitrary signed homogeneous coordinates.

The actual local p-adic covering that supplies these residue
classes remains a separate theorem.
-/

namespace DiophantineRigidity

/-- First projective chart: equal modular affine coordinates imply
cross determinant divisibility. -/
theorem first_chart_same_residue_cross_dvd
    (M : ℕ) (p q p' q' : ℤ) (z : ZMod M)
    (h₁ : (p : ZMod M) = z * (q : ZMod M))
    (h₂ : (p' : ZMod M) = z * (q' : ZMod M)) :
    (M : ℤ) ∣ p * q' - p' * q := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (p * q' - p' * q) M).mp
  have hcross :
      (p : ZMod M) * (q' : ZMod M) =
      (p' : ZMod M) * (q : ZMod M) := by
    rw [h₁, h₂]
    ring
  have hzero :
      (p : ZMod M) * (q' : ZMod M) -
      (p' : ZMod M) * (q : ZMod M) = 0 :=
    sub_eq_zero.mpr hcross
  simpa only [Int.cast_sub, Int.cast_mul] using hzero

/-- Reciprocal projective chart: q=z*p gives the same
cross determinant congruence. This includes primes dividing q,
for which the first chart may be unsuitable. -/
theorem second_chart_same_residue_cross_dvd
    (M : ℕ) (p q p' q' : ℤ) (z : ZMod M)
    (h₁ : (q : ZMod M) = z * (p : ZMod M))
    (h₂ : (q' : ZMod M) = z * (p' : ZMod M)) :
    (M : ℤ) ∣ p * q' - p' * q := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (p * q' - p' * q) M).mp
  have hcross :
      (p : ZMod M) * (q' : ZMod M) =
      (p' : ZMod M) * (q : ZMod M) := by
    rw [h₁, h₂]
    ring
  have hzero :
      (p : ZMod M) * (q' : ZMod M) -
      (p' : ZMod M) * (q : ZMod M) = 0 :=
    sub_eq_zero.mpr hcross
  simpa only [Int.cast_sub, Int.cast_mul] using hzero

end DiophantineRigidity
