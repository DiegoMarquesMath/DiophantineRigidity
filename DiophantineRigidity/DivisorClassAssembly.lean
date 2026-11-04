import Mathlib.NumberTheory.Divisors

/-!
# Counting by exact projective content divisors

The final aggregation in the projective-content lemma must count
each reduced rational argument once, partitioned by its exact
integer specialization content. This module establishes the
cardinality inequality over all positive divisors of the global
Bezout constant K.

The local p-adic class bounds and the analytic epsilon-divisor
estimate are separate inputs, and are not declared proved here.
-/

namespace DiophantineRigidity

/-- A finite family labeled by exact divisors of K can be counted
by summing over its fibers. The bound is stated in natural numbers
and works even if distinct fibers are empty. -/
theorem card_le_sum_over_content_divisors
    {α : Type*} [DecidableEq α]
    (S : Finset α) (K : ℕ) (content : α → ℕ)
    (bound : ℕ → ℕ)
    (hcontent : ∀ x ∈ S, content x ∈ K.divisors)
    (hbound : ∀ d ∈ K.divisors,
      (S.filter fun x => content x = d).card ≤ bound d) :
    S.card ≤ ∑ d ∈ K.divisors, bound d := by
  classical
  let part (d : ℕ) : Finset α :=
    S.filter fun x => content x = d
  have hcover : S = K.divisors.biUnion part := by
    ext x
    simp only [Finset.mem_biUnion, part, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨content x, hcontent x hx, hx, rfl⟩
    · rintro ⟨d, hd, hx, hdx⟩
      exact hx
  have hcard : S.card ≤ ∑ d ∈ K.divisors, (part d).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  calc
    S.card ≤ ∑ d ∈ K.divisors, (part d).card := hcard
    _ ≤ ∑ d ∈ K.divisors, bound d := by
      exact Finset.sum_le_sum (fun d hd => hbound d hd)

/-- The exact same aggregation restricted to exceptional points
whose content exceeds G. No artificial enlargement of the
denominator block or witness count occurs. -/
theorem card_le_sum_over_large_content_divisors
    {α : Type*} [DecidableEq α]
    (S : Finset α) (K G : ℕ) (content : α → ℕ)
    (bound : ℕ → ℕ)
    (hcontent : ∀ x ∈ S, content x ∈ K.divisors)
    (hlarge : ∀ x ∈ S, G < content x)
    (hbound : ∀ d ∈ K.divisors, G < d →
      (S.filter fun x => content x = d).card ≤ bound d) :
    S.card ≤ ∑ d ∈ K.divisors.filter (fun d => G < d), bound d := by
  classical
  let t : Finset ℕ := K.divisors.filter (fun d => G < d)
  have hmem : ∀ x ∈ S, content x ∈ t := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hcontent x hx, hlarge x hx⟩
  let part (d : ℕ) : Finset α :=
    S.filter fun x => content x = d
  have hcover : S = t.biUnion part := by
    ext x
    simp only [Finset.mem_biUnion, part, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨content x, hmem x hx, hx, rfl⟩
    · rintro ⟨d, hd, hx, hdx⟩
      exact hx
  have hcard : S.card ≤ ∑ d ∈ t, (part d).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  change S.card ≤ ∑ d ∈ t, bound d
  calc
    S.card ≤ ∑ d ∈ t, (part d).card := hcard
    _ ≤ ∑ d ∈ t, bound d := by
      exact Finset.sum_le_sum (fun d hd =>
        hbound d (Finset.mem_filter.mp hd).1
          (Finset.mem_filter.mp hd).2)

end DiophantineRigidity
