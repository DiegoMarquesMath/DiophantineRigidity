import Mathlib

/-!
# Abstract algebraic core of Hankel recovery (Lemma 3.2)

For a nonzero functional on a field, the multiplication pairing has
zero left radical. The later formalization must additionally prove
that the coefficient functionals descend to the quotient field,
recover the Hankel matrix, and produce an integral cofactor polynomial.
-/

namespace DiophantineRigidity

/-- Multiplication by a nonzero field element is bijective, so a
nonzero functional cannot vanish on all of its multiples. -/
theorem fieldMultiplication_nondegenerate
    {K : Type*} [Field K] (Λ : K → ℚ)
    (hΛ : ∃ z : K, Λ z ≠ 0)
    (u : K) (hu : u ≠ 0) :
    ∃ v : K, Λ (u * v) ≠ 0 := by
  obtain ⟨z, hz⟩ := hΛ
  refine ⟨u⁻¹ * z, ?_⟩
  simpa [mul_assoc, hu] using hz

/-- Equivalently, the left radical of the multiplication pairing
associated to a nonzero functional is {0}. -/
theorem fieldMultiplication_radical_eq_zero
    {K : Type*} [Field K] (Λ : K → ℚ)
    (hΛ : ∃ z : K, Λ z ≠ 0)
    (u : K) (hzero : ∀ v : K, Λ (u * v) = 0) :
    u = 0 := by
  by_contra hu
  obtain ⟨v, hv⟩ := fieldMultiplication_nondegenerate Λ hΛ u hu
  exact hv (hzero v)

end DiophantineRigidity
