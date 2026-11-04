import Mathlib

/-!
# Exact exponent identities in multiscale propagation (Lemma 5.1)

These algebraic identities record the interpolation-loss and resultant
degree budgets appearing in equation (5.6) of the manuscript.
They do not themselves prove any counting or propagation theorem.
-/

namespace DiophantineRigidity

/-- The identity omega+(k-1)*nu=k*theta*(1+2D+2s) for
nu=(1+2D)theta and omega=nu+2ks theta. -/
theorem propagation_loss_identity (k D s : ℕ) (θ : ℝ) :
    ((1 + 2 * (D : ℝ)) * θ + 2 * (k : ℝ) * (s : ℝ) * θ) +
      ((k : ℝ) - 1) * ((1 + 2 * (D : ℝ)) * θ) =
    (k : ℝ) * θ * (1 + 2 * (D : ℝ) + 2 * (s : ℝ)) := by
  ring

/-- The degree bound h<=k gives the negative exponent used when the
Sylvester resultant must be a nonzero integer. -/
theorem resultant_degree_margin (k h : ℕ) (w : ℝ)
    (hh : h ≤ k) :
    (k : ℝ) + (h : ℝ) - 1 - w ≤
      -(w - 2 * (k : ℝ) + 1) := by
  have hhr : (h : ℝ) ≤ (k : ℝ) := by exact_mod_cast hh
  linarith

end DiophantineRigidity
