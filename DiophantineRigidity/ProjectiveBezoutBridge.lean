import DiophantineRigidity.BezoutCertificates
import DiophantineRigidity.TwoChartDivisibility

/-!
# Integral Bezout identities after denominator clearing

A substantial arithmetic bridge towards Lemma 4.1 in
*Diophantine Rigidity of Analytic Graphs*.

Given an **integral** Bezout certificate for the Y-coefficients of
F(X,Y), we prove the exact specialized integer identity and the
resulting divisibility of the specialized polynomial content.
The construction and quantitative height bound of such a certificate
from coprimality are separate research obligations.

This file also combines distinct constants from the two projective
charts, which is essential for the subsequent uniform content bound.
-/

noncomputable section

namespace DiophantineRigidity

/-- A polynomial Bezout identity, evaluated at p/q and cleared of
both sets of denominators, remains an exact identity of integers.
The statement has no hidden assumption about primitivity. -/
theorem clearedBezout_sum_identity
    {ι : Type*} (s : Finset ι)
    (U A : ι → Polynomial ℤ) (K p q : ℤ) (D E : ℕ)
    (hq : q ≠ 0)
    (hU : ∀ j ∈ s, (U j).natDegree ≤ E)
    (hA : ∀ j ∈ s, (A j).natDegree ≤ D)
    (hcert : (∑ j ∈ s, U j * A j) = Polynomial.C K) :
    (∑ j ∈ s,
      clearedEvaluation (U j) p q E *
        clearedEvaluation (A j) p q D) =
      K * q ^ (D + E) := by
  classical
  have hr :
      (((∑ j ∈ s,
        clearedEvaluation (U j) p q E *
          clearedEvaluation (A j) p q D) : ℤ) : ℝ) =
        ((K * q ^ (D + E) : ℤ) : ℝ) := by
    calc
      (((∑ j ∈ s,
        clearedEvaluation (U j) p q E *
          clearedEvaluation (A j) p q D) : ℤ) : ℝ) =
          ∑ j ∈ s,
            (clearedEvaluation (U j) p q E : ℝ) *
              (clearedEvaluation (A j) p q D : ℝ) := by
                push_cast
                rfl
      _ = ∑ j ∈ s,
          ((q : ℝ) ^ E *
            (U j).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ))) *
          ((q : ℝ) ^ D *
            (A j).eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [clearedEvaluation_spec (U j) p q E (hU j hj) hq,
            clearedEvaluation_spec (A j) p q D (hA j hj) hq]
      _ = (q : ℝ) ^ E * (q : ℝ) ^ D *
          ((∑ j ∈ s, U j * A j : Polynomial ℤ).eval₂
            (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ))) := by
        simp only [Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (q : ℝ) ^ E * (q : ℝ) ^ D * (K : ℝ) := by
        rw [hcert]
        simp only [Polynomial.eval₂_C]
        rfl
      _ = ((K * q ^ (D + E) : ℤ) : ℝ) := by
        simp only [Int.cast_mul, Int.cast_pow]
        rw [pow_add]
        ring
  exact_mod_cast hr

/-- Given a genuine polynomial Bezout identity with integer constant
K, the content of the cleared specialization divides K times a power
of q, without any analytic or p-adic estimates. -/
theorem integerContent_dvd_Bezout_chart
    (F : Polynomial (Polynomial ℤ)) (U : ℕ → Polynomial ℤ)
    (K p q : ℤ) (D E : ℕ)
    (hq : q ≠ 0)
    (hF : ∀ j ∈ F.support, (F.coeff j).natDegree ≤ D)
    (hU : ∀ j ∈ F.support, (U j).natDegree ≤ E)
    (hcert :
      (∑ j ∈ F.support, U j * F.coeff j) = Polynomial.C K) :
    ((integerContent (clearedBivariate F p q D) : ℕ) : ℤ) ∣
      K * q ^ (D + E) := by
  have hsum :=
    clearedBezout_sum_identity F.support U (fun j => F.coeff j)
      K p q D E hq hU hF hcert
  rw [← hsum]
  apply Finset.dvd_sum
  intro j hj
  have hnat :
      integerContent (clearedBivariate F p q D) ∣
        (clearedEvaluation (F.coeff j) p q D).natAbs := by
    rw [← clearedBivariate_coeff F p q D j]
    exact integerContent_dvd_coeff _ j
  have hint :
      ((integerContent (clearedBivariate F p q D) : ℕ) : ℤ) ∣
        clearedEvaluation (F.coeff j) p q D := by
    rw [← Int.natAbs_dvd_natAbs]
    simpa using hnat
  exact dvd_mul_of_dvd_right hint _

/-- Two charts may have distinct integral certificate constants.
This is the exact arithmetic cancellation needed in Lemma 4.1,
once the corresponding two chartwise divisibilities are supplied. -/
theorem twoChart_dvd_product
    (g K₁ K₂ p q a b : ℕ) (hpq : Nat.Coprime p q)
    (hp : g ∣ K₁ * p ^ a)
    (hq : g ∣ K₂ * q ^ b) :
    g ∣ K₁ * K₂ := by
  have hp' : g ∣ (K₁ * K₂) * p ^ a := by
    calc
      g ∣ (K₁ * p ^ a) * K₂ := dvd_mul_of_dvd_left hp K₂
      _ = (K₁ * K₂) * p ^ a := by ring
  have hq' : g ∣ (K₁ * K₂) * q ^ b := by
    calc
      g ∣ (K₂ * q ^ b) * K₁ := dvd_mul_of_dvd_left hq K₁
      _ = (K₁ * K₂) * q ^ b := by ring
  exact twoChart_dvd_constant g (K₁ * K₂) p q a b hpq hp' hq'

end DiophantineRigidity
