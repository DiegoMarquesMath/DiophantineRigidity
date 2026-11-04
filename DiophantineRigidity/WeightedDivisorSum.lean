import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite weighted divisor sums in projective-content counting

The local p-adic cover produces at most (2D)^omega(g)
classes for a content divisor g. The first summation step is an
exact bound over divisors of the global certificate constant K.

The additional analytic number theory estimate
tau(K)*(2D)^omega(K) = O_(D,epsilon)(K^epsilon)
is not claimed here and remains a separate obligation.
-/

namespace DiophantineRigidity

/-- An exact finite weighted divisor bound. It is uniform in the
individual divisor g, since every prime factor of g divides K. -/
theorem weighted_divisor_sum_le
    (K D : ℕ) (hK : K ≠ 0) (hD : 0 < D) :
    (∑ g ∈ K.divisors, (2 * D) ^ g.primeFactors.card) ≤
      K.divisors.card * (2 * D) ^ K.primeFactors.card := by
  have hweight : ∀ g ∈ K.divisors,
      (2 * D) ^ g.primeFactors.card ≤
      (2 * D) ^ K.primeFactors.card := by
    intro g hg
    have hcard : g.primeFactors.card ≤ K.primeFactors.card :=
      Finset.card_le_card
        (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hg) hK)
    exact pow_le_pow_right₀ (by omega : 1 ≤ 2 * D) hcard
  calc
    (∑ g ∈ K.divisors, (2 * D) ^ g.primeFactors.card) ≤
        ∑ _g ∈ K.divisors, (2 * D) ^ K.primeFactors.card := by
          exact Finset.sum_le_sum hweight
    _ = K.divisors.card * (2 * D) ^ K.primeFactors.card := by
      simp [nsmul_eq_mul]

/-- In the degree-one case the unweighted divisor sum is exactly
the number of divisors. -/
theorem divisor_sum_one (K : ℕ) :
    (∑ _g ∈ K.divisors, (1 : ℕ)) = K.divisors.card := by
  simp

end DiophantineRigidity
