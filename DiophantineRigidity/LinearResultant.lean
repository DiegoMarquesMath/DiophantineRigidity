import Mathlib

/-!
# Linear integral resultants

A full formalization of Lemma 4.2 requires the general Sylvester
determinant and its evaluation bound. This file proves the degree-one
case directly, with no analytic hypotheses or upper bound on y.

For A(Y)=aY+b and P(Y)=cY+d, the determinant ad-bc is a nonzero
integer when the two linear polynomials are coprime.
-/

namespace DiophantineRigidity

/-- The degree-one instance of the integral resultant estimate.
The integer determinant is assumed nonzero; therefore its absolute
value is at least 1, and evaluating the two affine forms yields the bound. -/
theorem linearResultant_bound
    (a b c d : ℤ) (y : ℝ) (hdet : a * d - b * c ≠ 0) :
    (1 : ℝ) ≤
      |(a : ℝ) * y + (b : ℝ)| * |(c : ℝ)| +
      |(c : ℝ) * y + (d : ℝ)| * |(a : ℝ)| := by
  have hint : (1 : ℝ) ≤ |((a * d - b * c : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdet
  have hid :
      ((a * d - b * c : ℤ) : ℝ) =
        ((c : ℝ) * y + (d : ℝ)) * (a : ℝ) -
          ((a : ℝ) * y + (b : ℝ)) * (c : ℝ) := by
    push_cast
    ring
  rw [hid] at hint
  calc
    (1 : ℝ) ≤
        |((c : ℝ) * y + (d : ℝ)) * (a : ℝ) -
          ((a : ℝ) * y + (b : ℝ)) * (c : ℝ)| := hint
    _ ≤
        |((c : ℝ) * y + (d : ℝ)) * (a : ℝ)| +
        |((a : ℝ) * y + (b : ℝ)) * (c : ℝ)| := abs_sub _ _
    _ = _ := by
      rw [abs_mul, abs_mul]
      ring

end DiophantineRigidity
