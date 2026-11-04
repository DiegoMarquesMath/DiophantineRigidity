import Mathlib

/-!
# Congruence moduli and separation of rational arguments

This is the arithmetic counting bridge in the proof of projective
content Lemma 4.1. If all primes in a chosen divisor class force
a common modulus dividing the cross determinant of two rational
points, then the modulus controls their real separation.

The p-adic root-covering argument which *produces* these moduli,
and the final divisor-class summation, are independent obligations.
-/

namespace DiophantineRigidity

/-- Every positive modulus dividing a nonzero integer has size at
most its absolute value. Applied below to cross determinants. -/
theorem modulus_le_cross_natAbs
    (p p' q q' : ℤ) (M : ℕ)
    (hne : p * q' - p' * q ≠ 0)
    (hdvd : (M : ℤ) ∣ p * q' - p' * q) :
    M ≤ (p * q' - p' * q).natAbs := by
  apply Nat.le_of_dvd
  · exact Int.natAbs_pos.mpr hne
  · simpa using (Int.natAbs_dvd_natAbs).mpr hdvd

/-- Modulus divisibility of the cross determinant implies real
separation. In contrast to ordinary Farey spacing, the factor M
is retained. No restriction on numerators or coprimality is needed. -/
theorem cross_modulus_real_separation
    (p p' : ℤ) (q q' M : ℕ)
    (hq : 0 < q) (hq' : 0 < q')
    (hne : p * (q' : ℤ) - p' * (q : ℤ) ≠ 0)
    (hdvd : (M : ℤ) ∣ p * (q' : ℤ) - p' * (q : ℤ)) :
    (M : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤
      |(p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)| := by
  let z : ℤ := p * (q' : ℤ) - p' * (q : ℤ)
  have hz : M ≤ z.natAbs := by
    exact modulus_le_cross_natAbs p p' q q' M hne hdvd
  have hzR : (M : ℝ) ≤ |(z : ℝ)| := by
    have hzR' : (M : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hz
    simpa only [Int.cast_natAbs, Int.cast_abs] using hzR'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hden : (0 : ℝ) < (q : ℝ) * q' := mul_pos hqR hq'R
  have heq :
      (p : ℝ) / q - (p' : ℝ) / q' =
        (z : ℝ) / ((q : ℝ) * q') := by
    dsimp [z]
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).mpr hzR


/-- The Chinese remainder arithmetic step: two coprime moduli
dividing the same integer cross determinant have a product
which also divides it. This handles a pair of prime-power
congruence conditions without any analytic hypotheses. -/
theorem coprime_moduli_mul_dvd_cross
    (a b : ℕ) (z : ℤ)
    (hcop : Nat.Coprime a b)
    (ha : (a : ℤ) ∣ z) (hb : (b : ℤ) ∣ z) :
    ((a * b : ℕ) : ℤ) ∣ z := by
  have haN : a ∣ z.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr ha
  have hbN : b ∣ z.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hb
  have hN : a * b ∣ z.natAbs :=
    hcop.mul_dvd_of_dvd_of_dvd haN hbN
  rw [← Int.natAbs_dvd_natAbs]
  simpa using hN

/-- Two coprime prime-power congruence conditions combine
into one strengthened separation inequality. -/
theorem coprime_moduli_real_separation
    (p p' : ℤ) (q q' a b : ℕ)
    (hq : 0 < q) (hq' : 0 < q')
    (hne : p * (q' : ℤ) - p' * (q : ℤ) ≠ 0)
    (hcop : Nat.Coprime a b)
    (ha : (a : ℤ) ∣ p * (q' : ℤ) - p' * (q : ℤ))
    (hb : (b : ℤ) ∣ p * (q' : ℤ) - p' * (q : ℤ)) :
    ((a * b : ℕ) : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤
      |(p : ℝ) / (q : ℝ) - (p' : ℝ) / (q' : ℝ)| :=
  cross_modulus_real_separation p p' q q' (a * b) hq hq'
    hne (coprime_moduli_mul_dvd_cross a b _ hcop ha hb)

end DiophantineRigidity
