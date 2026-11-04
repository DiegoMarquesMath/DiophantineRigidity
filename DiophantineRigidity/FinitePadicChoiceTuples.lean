import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite choice-tuples in the projective p-adic covering

Given a finite set of prime factors and at most 2D chart-and-root
choices for each prime, the total number of choice-tuples is
at most (2D)^omega(g).

This theorem derives the combinatorial count *from actual finite
choice sets*. It does not postulate that the p-adic polynomial
solutions have such finite covers: existence of the cover is the
separate Lagrange-interpolation obligation.
-/

namespace DiophantineRigidity

/-- The Cartesian product of finite chart-and-root class choices
has at most (2D)^|s| elements when each individual choice set has
cardinality at most 2D. -/
theorem finite_padic_choice_tuples_card_le
    {ι τ : Type*} [DecidableEq ι]
    (s : Finset ι) (classes : ι → Finset τ) (D : ℕ)
    (hclasses : ∀ i ∈ s, (classes i).card ≤ 2 * D) :
    (s.pi classes).card ≤ (2 * D) ^ s.card := by
  classical
  rw [Finset.card_pi]
  calc
    (∏ i ∈ s, (classes i).card) ≤
        ∏ _i ∈ s, (2 * D) := by
      exact Finset.prod_le_prod' hclasses
    _ = (2 * D) ^ s.card := by
      simp

end DiophantineRigidity
