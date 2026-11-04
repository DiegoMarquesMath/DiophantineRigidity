import MahlerLean.FareySeparation
import MahlerLean.CurrentTheoremOne

/-!
# Precisely scoped reuse of earlier verified results

These imported theorems were established in the independent MahlerLean
project. In particular, the entire-function result below is inherited
from the earlier proof, NOT from the as-yet-unproved arbitrary-degree
S-number theorem of the new manuscript.
-/

noncomputable section
namespace DiophantineRigidity

/-- Spacing of distinct reduced rationals, proved by the old project. -/
theorem reducedRationalSpacing (r s : ℚ) (hrs : r ≠ s) :
    1 / ((r.den : ℝ) * (s.den : ℝ)) ≤ |(r : ℝ) - (s : ℝ)| :=
  MahlerLean.rational_separation r s hrs

/-- The earlier formalized entire-function rigidity statement.
The new manuscript's deduction through its stronger Cantor theorem
remains a separate formalization obligation. -/
theorem entireRigidityFromLegacy
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hpres : ∀ x : ℝ, Liouville x →
      ∃ y : ℝ, Liouville y ∧ F x = y) :
    ∃ P : Polynomial ℝ, ∀ z : ℂ,
      F z = P.eval₂ Complex.ofRealHom z :=
  MahlerLean.current_theorem_1_3 hF hpres

end DiophantineRigidity
