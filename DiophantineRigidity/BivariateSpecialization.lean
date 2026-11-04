import DiophantineRigidity.ArithmeticSpecialization

/-!
# Denominator clearing of a bivariate integer polynomial

We represent F(X,Y) by Polynomial (Polynomial ℤ), where the outer
variable is Y. Every X-coefficient has degree at most D.
The resulting polynomial has integer coefficients *by construction*.

This is the exact algebraic specialization, not a bound on its content.
-/

noncomputable section
namespace DiophantineRigidity

/-- Integer polynomial obtained by clearing denominators in every
Y-coefficient of F(p/q,Y) using the same X-degree bound D. -/
def clearedBivariate (F : Polynomial (Polynomial ℤ)) (p q : ℤ)
    (D : ℕ) : Polynomial ℤ :=
  Polynomial.ofFinsupp
    (Finsupp.onFinset F.support
      (fun j => clearedEvaluation (F.coeff j) p q D)
      (by
        intro j hj
        by_contra hn
        have hzero : F.coeff j = 0 :=
          Polynomial.notMem_support_iff.mp hn
        have hv : clearedEvaluation (F.coeff j) p q D = 0 := by
          simp [hzero, clearedEvaluation]
        exact hj hv))

/-- The coefficient of Y^j is the integer obtained by clearing the
denominator in the corresponding X-polynomial. -/
theorem clearedBivariate_coeff
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D j : ℕ) :
    (clearedBivariate F p q D).coeff j =
      clearedEvaluation (F.coeff j) p q D := by
  rfl

/-- Each coefficient specializes to q^D F_j(p/q), where F_j is the
coefficient of Y^j in F. -/
theorem clearedBivariate_coeff_spec
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D j : ℕ)
    (hdegree : (F.coeff j).natDegree ≤ D) (hq : q ≠ 0) :
    ((clearedBivariate F p q D).coeff j : ℝ) =
      (q : ℝ) ^ D *
        (F.coeff j).eval₂ (Int.castRingHom ℝ)
          ((p : ℝ) / (q : ℝ)) := by
  rw [clearedBivariate_coeff]
  exact clearedEvaluation_spec (F.coeff j) p q D hdegree hq

/-- Nonvanishing of any coefficient evaluation excludes the zero
specialization. This is later supplied by a polynomial gcd/Bezout
certificate, not assumed in the final projective-content lemma. -/
theorem clearedBivariate_ne_zero_of_coefficient
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D : ℕ)
    (hdegree : ∀ j, (F.coeff j).natDegree ≤ D) (hq : q ≠ 0)
    (hcoeff : ∃ j, (F.coeff j).eval₂ (Int.castRingHom ℝ)
        ((p : ℝ) / (q : ℝ)) ≠ 0) :
    clearedBivariate F p q D ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hcoeff
  have hzero : ((clearedBivariate F p q D).coeff j : ℝ) = 0 := by
    simp [hz]
  rw [clearedBivariate_coeff_spec F p q D j (hdegree j) hq] at hzero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  exact hj ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero D hqR))

end DiophantineRigidity
