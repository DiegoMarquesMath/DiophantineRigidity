import MahlerLean.FareyCounting

/-!
# Farey packing for the new manuscript

Exact reuse of the already machine-checked rational separation and
finite-union packing estimates from MahlerLean.

The first theorem is the one-interval part of equation (2.3).
The finite-union theorem is stated for a supplied decomposition
into order-connected, pairwise disjoint components. It makes no
unproved assertion that arbitrary sublevel sets have such a
decomposition: that is a separate analytic lemma.
-/

noncomputable section

namespace DiophantineRigidity

open Set MeasureTheory
open scoped ENNReal

/-- The precise one-interval spacing estimate needed in Section 2. -/
theorem farey_interval_bound (l u : ℝ) (Q : ℕ)
    (hlu : l ≤ u) (hQ : 0 < Q) :
    ((MahlerLean.sourceFractions l u Q).card : ℝ) ≤
      4 * (Q : ℝ) ^ 2 * (u - l) + 1 :=
  MahlerLean.sourceFractions_card_le l u Q hlu hQ

/-- The finite-disjoint-union spacing estimate (2.3).
The decomposition and its finite measure are explicit hypotheses. -/
theorem farey_union_bound {ι : Type*}
    (t : Finset ι) (E : ι → Set ℝ) (S : Finset ℚ)
    (Q R : ℕ) (hQ : 0 < Q) (hR : t.card ≤ R)
    (hintervals : ∀ i ∈ t, OrdConnected (E i))
    (hdisjoint : Set.PairwiseDisjoint (t : Set ι) E)
    (hcover : ∀ r ∈ S, ∃ i ∈ t, (r : ℝ) ∈ E i)
    (hden : ∀ r ∈ S, r.den < 2 * Q)
    (hfinite : volume (⋃ i ∈ t, E i) ≠ ∞) :
    (S.card : ℝ) ≤
      4 * (Q : ℝ) ^ 2 *
        (volume (⋃ i ∈ t, E i)).toReal + R :=
  MahlerLean.rational_union_card_le
    t E S Q R hQ hR hintervals hdisjoint hcover hden hfinite

end DiophantineRigidity
