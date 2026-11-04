import DiophantineRigidity.CongruenceSpacing

/-!
# Exact congruences from linear projective-chart specializations

At X-degree one the homogenized value of V(X) = a X + b
at the primitive pair (p,q) is a*p+b*q.
For two specializations divisible by M, elimination of b gives
M | a*(p*q' - p'*q).  If a is a unit modulo M,
Euclid's lemma removes a and yields the cross-determinant congruence.

This is the unconditional (on the two evaluations) arithmetic
mechanism of the D=1 case. No p-adic root-covering hypothesis is used.
-/

namespace DiophantineRigidity

/-- Elimination of the constant coefficient from two homogenized
linear specializations. This identity works for signed coordinates
and arbitrary nonzero or zero moduli. -/
theorem linear_chart_dvd_coefficient_cross
    (a b p q p' q' M : ℤ)
    (h₁ : M ∣ a * p + b * q)
    (h₂ : M ∣ a * p' + b * q') :
    M ∣ a * (p * q' - p' * q) := by
  have h := dvd_sub
    (dvd_mul_of_dvd_left h₁ q')
    (dvd_mul_of_dvd_left h₂ q)
  have heq :
      (a * p + b * q) * q' - (a * p' + b * q') * q =
      a * (p * q' - p' * q) := by ring
  rw [heq] at h
  exact h

/-- For a linear chart polynomial whose leading coefficient is
coprime to the modulus, both vanishing congruences force the
required modular separation of the rational arguments.

The unit condition is a concrete arithmetic hypothesis, not a
root-covering or cardinality assumption. -/
theorem linear_chart_dvd_cross
    (a b p q p' q' M : ℤ)
    (hunit : Int.gcd M a = 1)
    (h₁ : M ∣ a * p + b * q)
    (h₂ : M ∣ a * p' + b * q') :
    M ∣ p * q' - p' * q := by
  have h := linear_chart_dvd_coefficient_cross
    a b p q p' q' M h₁ h₂
  exact Int.dvd_of_dvd_mul_right_of_gcd_one h hunit

end DiophantineRigidity
