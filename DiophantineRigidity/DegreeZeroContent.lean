import DiophantineRigidity.IntegerContent
import DiophantineRigidity.BivariateSpecialization

/-!
# Degree-zero projective content

For X-degree D = 0, denominator-cleared specialization is
independent of the rational argument. Consequently the integer
coefficient content stays equal to the content at the reference
specialization (p,q) = (0,1).

This establishes the D=0 endpoint of the projective-content lemma
once global primitivity is represented by the exact coefficient gcd.
-/

namespace DiophantineRigidity

/-- At X-degree zero, clearing denominators is simply coefficient
extraction; it does not depend on either p or q. -/
theorem clearedEvaluation_zero_degree
    (P : Polynomial ℤ) (p q : ℤ) :
    clearedEvaluation P p q 0 = P.coeff 0 := by
  simp [clearedEvaluation]

/-- Every Y-coefficient of a zero-degree specialization is invariant
under changes of the rational argument, even for q=0. -/
theorem clearedBivariate_zero_degree_eq
    (F : Polynomial (Polynomial ℤ)) (p q p' q' : ℤ) :
    clearedBivariate F p q 0 = clearedBivariate F p' q' 0 := by
  apply Polynomial.ext
  intro j
  simp only [clearedBivariate_coeff, clearedEvaluation_zero_degree]

/-- The D=0 content is exactly constant. If the coefficient
polynomial is primitive at one reference specialization, then its
content is one at every rational argument. -/
theorem integerContent_eq_one_of_zero_degree_primitive
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ)
    (hprimitive : integerContent (clearedBivariate F 0 1 0) = 1) :
    integerContent (clearedBivariate F p q 0) = 1 := by
  rw [clearedBivariate_zero_degree_eq F p q 0 1]
  exact hprimitive

end DiophantineRigidity
