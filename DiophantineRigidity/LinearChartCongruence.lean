import DiophantineRigidity.ModularFareyPacking

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


/-- Elimination of the leading coefficient instead of the constant
coefficient. Together with the preceding theorem, this gives
divisibility by every coefficient of a linear polynomial. -/
theorem linear_chart_dvd_constant_cross
    (a b p q p' q' M : ℤ)
    (h₁ : M ∣ a * p + b * q)
    (h₂ : M ∣ a * p' + b * q') :
    M ∣ b * (p * q' - p' * q) := by
  have h := dvd_sub
    (dvd_mul_of_dvd_left h₂ p)
    (dvd_mul_of_dvd_left h₁ p')
  have heq :
      (a * p' + b * q') * p - (a * p + b * q) * p' =
        b * (p * q' - p' * q) := by ring
  rw [heq] at h
  exact h

/-- A primitive coefficient family with an explicit integral linear
combination equal to one forces the full cross-determinant congruence.
No individual coefficient needs to be invertible modulo M.

This is the decisive degree-one arithmetic reduction in Lemma 4.1.
The certificate is ordinary integer Bézout data and can be obtained
from the primitive coefficient gcd by Euclid's algorithm. -/
theorem linear_family_dvd_cross_of_integer_certificate
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b u v : ι → ℤ) (p q p' q' M : ℤ)
    (hcert : (∑ j ∈ s, (u j * a j + v j * b j)) = 1)
    (hfirst : ∀ j ∈ s, M ∣ a j * p + b j * q)
    (hsecond : ∀ j ∈ s, M ∣ a j * p' + b j * q') :
    M ∣ p * q' - p' * q := by
  let z : ℤ := p * q' - p' * q
  have hsum : M ∣ ∑ j ∈ s, (u j * a j + v j * b j) * z := by
    apply Finset.dvd_sum
    intro j hj
    have ha : M ∣ a j * z :=
      linear_chart_dvd_coefficient_cross
        (a j) (b j) p q p' q' M (hfirst j hj) (hsecond j hj)
    have hb : M ∣ b j * z :=
      linear_chart_dvd_constant_cross
        (a j) (b j) p q p' q' M (hfirst j hj) (hsecond j hj)
    have h₁ : M ∣ (u j) * (a j * z) :=
      dvd_mul_of_dvd_right ha (u j)
    have h₂ : M ∣ (v j) * (b j * z) :=
      dvd_mul_of_dvd_right hb (v j)
    convert dvd_add h₁ h₂ using 1 <;> ring
  have hfactor : (∑ j ∈ s, (u j * a j + v j * b j) * z) =
      (∑ j ∈ s, (u j * a j + v j * b j)) * z := by
    rw [Finset.sum_mul]
  rw [hfactor, hcert, one_mul] at hsum
  exact hsum


/-- For a degree-one coefficient family with integer Bézout
certificate, every common congruence divisor M gives an
explicit power-saving packing bound on the corresponding rational
arguments. There is no p-adic root-covering assumption.

This closes the fixed-divisor counting argument for X-degree one;
the final summation over divisors of a global certificate constant
is a distinct step. -/
theorem linear_family_modular_farey_count
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (a b u v : ι → ℤ)
    (S : Finset ℚ) (l h : ℝ) (Q M : ℕ)
    (hlh : l ≤ h) (hQ : 0 < Q) (hM : 0 < M)
    (hcert : (∑ j ∈ indices, (u j * a j + v j * b j)) = 1)
    (hmem : ∀ r ∈ S, l ≤ (r : ℝ) ∧ (r : ℝ) ≤ h)
    (hden : ∀ r ∈ S, r.den < 2 * Q)
    (hdiv : ∀ r ∈ S, ∀ j ∈ indices,
      (M : ℤ) ∣ a j * r.num + b j * (r.den : ℤ)) :
    (S.card : ℝ) ≤
      (h - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1 := by
  apply modular_farey_interval_card_le S l h Q M
    hlh hQ hM hmem hden
  intro r hr s hs hrs
  exact linear_family_dvd_cross_of_integer_certificate
    indices a b u v r.num (r.den : ℤ) s.num (s.den : ℤ) (M : ℤ)
    hcert (fun j hj => hdiv r hr j hj)
    (fun j hj => hdiv s hs j hj)

end DiophantineRigidity
