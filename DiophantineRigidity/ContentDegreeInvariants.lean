import DiophantineRigidity.IntegerContent
import DiophantineRigidity.BivariateSpecialization

/-!
# Contents and degree under specialization

These algebraic invariants make the degenerate cases explicit:
* the integer content vanishes exactly on the zero polynomial;
* the denominator-cleared specialization cannot increase Y-degree.

They are prerequisites for the full projective-content and resultant
arguments, not the full counting theorem.
-/

noncomputable section
namespace DiophantineRigidity

/-- The content of an integer polynomial is zero exactly when
the polynomial itself is zero. -/
theorem integerContent_eq_zero_iff (P : Polynomial ℤ) :
    integerContent P = 0 ↔ P = 0 := by
  classical
  constructor
  · intro hz
    have hcontent :
        (P.support.gcd (fun j => (P.coeff j).natAbs)) = 0 := hz
    have hzero :
        ∀ j ∈ P.support, (P.coeff j).natAbs = 0 :=
      (Finset.gcd_eq_zero_iff).mp hcontent
    apply Polynomial.ext
    intro j
    by_cases hj : j ∈ P.support
    · have hc : P.coeff j = 0 :=
        Int.natAbs_eq_zero.mp (hzero j hj)
      simp [hc]
    · have hc : P.coeff j = 0 :=
        Polynomial.notMem_support_iff.mp hj
      simp [hc]
  · intro hz
    rw [hz]
    simp [integerContent]

/-- A nonzero integer polynomial has positive coefficient content. -/
theorem integerContent_pos_of_ne_zero (P : Polynomial ℤ) (hP : P ≠ 0) :
    0 < integerContent P := by
  have hne : integerContent P ≠ 0 := by
    intro hzero
    exact hP ((integerContent_eq_zero_iff P).mp hzero)
  exact Nat.pos_of_ne_zero hne

/-- Clearing the X-denominators cannot increase the degree in Y,
including the case where the specialization becomes zero. -/
theorem clearedBivariate_degree_le
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D : ℕ) :
    (clearedBivariate F p q D).degree ≤ F.degree := by
  apply (Polynomial.degree_le_iff_coeff_zero
    (clearedBivariate F p q D) F.degree).mpr
  intro j hj
  have hcoeff : F.coeff j = 0 :=
    (Polynomial.degree_le_iff_coeff_zero F F.degree).mp le_rfl j hj
  rw [clearedBivariate_coeff, hcoeff]
  simp [clearedEvaluation]

/-- The corresponding natural-degree inequality. -/
theorem clearedBivariate_natDegree_le
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D : ℕ) :
    (clearedBivariate F p q D).natDegree ≤ F.natDegree :=
  Polynomial.natDegree_le_natDegree
    (clearedBivariate_degree_le F p q D)

end DiophantineRigidity
