import DiophantineRigidity.IntegerContent

/-!
# Arithmetic intersection of the two projective charts

This elementary but essential step in Lemma 4.1 says that a common
divisor of K p^a and K q^b must divide K when p,q are coprime.
The two Bezout certificates required to supply those divisibilities
are separate obligations of the full projective-content proof.
-/

namespace DiophantineRigidity

/-- The two projective charts together eliminate the extra powers
of coprime coordinates. The exponents may be zero. -/
theorem twoChart_dvd_constant
    (g K p q a b : ℕ) (hpq : Nat.Coprime p q)
    (hp : g ∣ K * p ^ a) (hq : g ∣ K * q ^ b) :
    g ∣ K := by
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    (hpq.pow_left a).pow_right b
  have hcommon : g ∣ Nat.gcd (K * p ^ a) (K * q ^ b) :=
    Nat.dvd_gcd hp hq
  have hgcd : Nat.gcd (p ^ a) (q ^ b) = 1 := hcop
  simpa [Nat.gcd_mul_left, hgcd] using hcommon

/-- Applied to the content of a polynomial: chartwise divisibility
by the same fixed constant implies unconditional divisibility. -/
theorem integerContent_dvd_constant_of_twoCharts
    (R : Polynomial ℤ) (K p q a b : ℕ)
    (hpq : Nat.Coprime p q)
    (hp : integerContent R ∣ K * p ^ a)
    (hq : integerContent R ∣ K * q ^ b) :
    integerContent R ∣ K :=
  twoChart_dvd_constant (integerContent R) K p q a b hpq hp hq

end DiophantineRigidity
