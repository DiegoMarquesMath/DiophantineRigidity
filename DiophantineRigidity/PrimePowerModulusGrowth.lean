import Mathlib

/-!
# Prime-power moduli and the sharp exponent 1/D

For a prescribed finite family of distinct prime powers, the product
of their ceiling-exponent moduli has D-th power at least the original
product. This numeric fact is independent of the (still pending)
p-adic root-class covering theorem.

The instance of ordered ceiling division is supplied by mathlib.
-/

namespace DiophantineRigidity

/-- Ceiling division is the *minimal* multiplier threshold:
for D>0, one has b ≤ D*ceil(b/D). -/
theorem exponent_le_degree_mul_ceil
    (D b : ℕ) (hD : 0 < D) :
    b ≤ D * (b ⌈/⌉ D) := by
  simpa only [nsmul_eq_mul] using
    (le_smul_ceilDiv (a := D) (b := b) hD)

/-- Each prime power divides a suitably large ceiling-exponent
modulus power. The only size requirement is ℓ≥1. -/
theorem prime_power_le_ceiling_modulus_pow
    (ℓ D b : ℕ) (hℓ : 0 < ℓ) (hD : 0 < D) :
    ℓ ^ b ≤ (ℓ ^ (b ⌈/⌉ D)) ^ D := by
  calc
    ℓ ^ b ≤ ℓ ^ (D * (b ⌈/⌉ D)) := by
      exact pow_le_pow_right₀ (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hℓ))
        (exponent_le_degree_mul_ceil D b hD)
    _ = (ℓ ^ (b ⌈/⌉ D)) ^ D := by
      rw [mul_comm D, pow_mul]

/-- The product of the modulus contributions controls the original
product of prime powers, giving the exact exponent 1/D after taking
real D-th roots. No assumption that the primes are distinct is needed
for this purely numeric inequality. -/
theorem product_prime_powers_le_modulus_pow
    {ι : Type*} (s : Finset ι)
    (prime exponent : ι → ℕ) (D : ℕ)
    (hD : 0 < D)
    (hprime : ∀ i ∈ s, 0 < prime i) :
    (∏ i ∈ s, prime i ^ exponent i) ≤
      (∏ i ∈ s, prime i ^ (exponent i ⌈/⌉ D)) ^ D := by
  calc
    (∏ i ∈ s, prime i ^ exponent i) ≤
      ∏ i ∈ s, (prime i ^ (exponent i ⌈/⌉ D)) ^ D := by
        apply Finset.prod_le_prod'
        intro i hi
        exact prime_power_le_ceiling_modulus_pow (prime i) D (exponent i)
          (hprime i hi) hD
    _ = (∏ i ∈ s, prime i ^ (exponent i ⌈/⌉ D)) ^ D := by
      rw [Finset.prod_pow]

end DiophantineRigidity
