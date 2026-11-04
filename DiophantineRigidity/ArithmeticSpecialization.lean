import DiophantineRigidity.Witnesses

/-!
# Clearing denominators in polynomial specializations

Section 2 / the first arithmetic ingredient of Lemma 4.1 in
*Diophantine Rigidity of Analytic Graphs*.

This module proves an exact identity, not just an asymptotic estimate.
The polynomial need not be monic or primitive. The parameter D is an
upper degree bound and q may be any nonzero integer.

The full projective-content estimate of Lemma 4.1 remains open.
-/

noncomputable section

namespace DiophantineRigidity

/-- The integral homogeneous evaluation obtained by multiplying an integer
polynomial value at p/q by q^D, where D bounds the degree. -/
def clearedEvaluation (P : Polynomial ℤ) (p q : ℤ) (D : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (D + 1), P.coeff i * p ^ i * q ^ (D - i)

/-- The exact clearing-denominators identity for integer polynomials.
No assumption of primitivity or irreducibility is needed. -/
theorem clearedEvaluation_spec (P : Polynomial ℤ) (p q : ℤ) (D : ℕ)
    (hdegree : P.natDegree ≤ D) (hq : q ≠ 0) :
    (clearedEvaluation P p q D : ℝ) =
      (q : ℝ) ^ D *
        P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ)) := by
  classical
  have hn : P.natDegree < D + 1 := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℝ) hn
    ((p : ℝ) / (q : ℝ))]
  unfold clearedEvaluation
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i ≤ D := by
    have h := Finset.mem_range.mp hi
    omega
  have hpow : (q : ℝ) ^ D =
      (q : ℝ) ^ (D - i) * (q : ℝ) ^ i := by
    calc
      (q : ℝ) ^ D = (q : ℝ) ^ (D - i + i) := by
        rw [Nat.sub_add_cancel hiD]
      _ = (q : ℝ) ^ (D - i) * (q : ℝ) ^ i := pow_add _ _ _
  rw [hpow, div_pow]
  field_simp [hqR]
  change (P.coeff i : ℝ) * (p : ℝ) ^ i =
    (p : ℝ) ^ i * (P.coeff i : ℝ)
  exact mul_comm _ _

/-- The scaled value is an integer. This is the form used when taking
integer contents of the Y-coefficients of a bivariate specialization. -/
theorem exists_integer_cleared_evaluation
    (P : Polynomial ℤ) (p q : ℤ) (D : ℕ)
    (hdegree : P.natDegree ≤ D) (hq : q ≠ 0) :
    ∃ a : ℤ,
      (a : ℝ) = (q : ℝ) ^ D *
        P.eval₂ (Int.castRingHom ℝ) ((p : ℝ) / (q : ℝ)) :=
  ⟨clearedEvaluation P p q D,
    clearedEvaluation_spec P p q D hdegree hq⟩

/-- Coefficientwise denominator clearing for a bivariate integer
polynomial represented as a polynomial in Y with X-polynomial
coefficients. This does not claim that the resulting content is small. -/
theorem exists_integer_cleared_coefficient
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D j : ℕ)
    (hdegree : (F.coeff j).natDegree ≤ D) (hq : q ≠ 0) :
    ∃ a : ℤ,
      (a : ℝ) = (q : ℝ) ^ D *
        (F.coeff j).eval₂ (Int.castRingHom ℝ)
          ((p : ℝ) / (q : ℝ)) :=
  exists_integer_cleared_evaluation (F.coeff j) p q D hdegree hq

end DiophantineRigidity
