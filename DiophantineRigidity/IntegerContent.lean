import DiophantineRigidity.ArithmeticSpecialization
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Integer coefficient content

The content is the nonnegative gcd of the absolute integer coefficients.
Zero coefficients and the zero polynomial are included in the definition.
These facts will be used when comparing a primitive witness with a
denominator-cleared bivariate specialization in Lemma 4.1.

This module does not prove the projective-content counting estimate.
-/

namespace DiophantineRigidity

/-- Nonnegative gcd of the coefficients of an integer polynomial. -/
noncomputable def integerContent (P : Polynomial ℤ) : ℕ :=
  P.support.gcd (fun i => (P.coeff i).natAbs)

/-- The content divides every coefficient, including those outside
the finite support (which are zero). -/
theorem integerContent_dvd_coeff (P : Polynomial ℤ) (j : ℕ) :
    integerContent P ∣ (P.coeff j).natAbs := by
  classical
  by_cases hj : j ∈ P.support
  · exact Finset.gcd_dvd hj
  · have hzero : P.coeff j = 0 :=
      Polynomial.notMem_support_iff.mp hj
    simp [hzero]

/-- A positive integer divides the content exactly when it divides
every coefficient. In fact the equivalence holds for every natural
number, including zero. -/
theorem dvd_integerContent_iff (P : Polynomial ℤ) (g : ℕ) :
    g ∣ integerContent P ↔
      ∀ j : ℕ, g ∣ (P.coeff j).natAbs := by
  classical
  constructor
  · intro h j
    exact dvd_trans h (integerContent_dvd_coeff P j)
  · intro h
    exact Finset.dvd_gcd (fun j _ => h j)

end DiophantineRigidity
