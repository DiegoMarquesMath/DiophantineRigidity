import DiophantineRigidity.SylvesterHeightBound

/-!
# Integral-to-complex base change for Sylvester resultants

The Sylvester determinant is an integer. Its image under the canonical
inclusion ℤ→ℂ is the determinant of the mapped coefficient polynomials.

This statement uses the *same nominal degree parameters* D,e on both
sides, so specialization degree drops are not silently normalized.

The algebraic nonzero resultant theorem and the root-avoidance
construction occur in other PRs; this file provides the exact bridge.
-/

namespace DiophantineRigidity

/-- The Sylvester matrix commutes with the injective ring morphism
from integer coefficients into the complex numbers. -/
theorem sylvester_integer_to_complex
    (A W : Polynomial ℤ) (D e : ℕ) :
    Polynomial.sylvester
        (A.map (Int.castRingHom ℂ))
        (W.map (Int.castRingHom ℂ)) D e =
      (Int.castRingHom ℂ).mapMatrix (Polynomial.sylvester A W D e) := by
  classical
  ext i j
  refine Fin.addCases ?_ ?_ j
  · intro j₁
    simp [Polynomial.sylvester, Fin.addCases_left]
  · intro j₁
    simp [Polynomial.sylvester, Fin.addCases_right]

/-- The exact integral resultant maps to the complex resultant
without changing the declared polynomial-degree parameters. -/
theorem resultant_integer_to_complex
    (A W : Polynomial ℤ) (D e : ℕ) :
    ((Polynomial.resultant A W D e : ℤ) : ℂ) =
      Polynomial.resultant
        (A.map (Int.castRingHom ℂ))
        (W.map (Int.castRingHom ℂ)) D e := by
  unfold Polynomial.resultant
  rw [sylvester_integer_to_complex A W D e]
  exact (RingHom.map_det (Int.castRingHom ℂ)
    (Polynomial.sylvester A W D e))

/-- A nonzero complex resultant guarantees that the actual integer
resultant is nonzero, for the same D,e. -/
theorem resultant_integer_ne_zero_of_complex
    (A W : Polynomial ℤ) (D e : ℕ)
    (h : Polynomial.resultant
      (A.map (Int.castRingHom ℂ))
      (W.map (Int.castRingHom ℂ)) D e ≠ 0) :
    Polynomial.resultant A W D e ≠ 0 := by
  intro hz
  apply h
  rw [← resultant_integer_to_complex A W D e, hz]
  norm_num

end DiophantineRigidity
