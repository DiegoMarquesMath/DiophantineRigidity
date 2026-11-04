import Mathlib
import MahlerLean.RationalBlocks

/-!
# Polynomial witnesses for the new analytic-graphs count

Definitions only: this file does not claim the new counting theorem.
Every source rational is counted once. Exact polynomial zeros and
nonprimitive integer witnesses are included.
-/

noncomputable section
namespace DiophantineRigidity

/-- Naive height: largest absolute integer coefficient. -/
def naiveHeight (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)

/-- Evaluation of an integer polynomial at a real number. -/
def polynomialValue (P : Polynomial ℤ) (y : ℝ) : ℝ :=
  P.eval₂ (Int.castRingHom ℝ) y

/-- The exact witness predicate with *independent* polynomial height B
and denominator block Q. P is nonzero and exact zeros are allowed. -/
def HasPolynomialWitness (f : ℝ → ℝ) (r : ℚ)
    (m : ℕ) (B w L : ℝ) : Prop :=
  ∃ P : Polynomial ℤ,
    P ≠ 0 ∧
    P.natDegree ≤ m ∧
    B ≤ (naiveHeight P : ℝ) ∧
    (naiveHeight P : ℝ) < 2 * B ∧
    |polynomialValue P (f (r : ℝ))| ≤ L * B ^ (-w)

/-- Exceptional reduced rational arguments in [l,u] with canonical
reduced denominator in [Q,2Q). Multiple witnesses count only once. -/
def exceptionalArguments (f : ℝ → ℝ) (l u : ℝ)
    (Q m : ℕ) (B w L : ℝ) : Finset ℚ := by
  classical
  exact (MahlerLean.sourceFractions l u Q).filter
    (fun r => HasPolynomialWitness f r m B w L)

/-- Characterization of the exceptional set, without strengthening
its hypotheses or modifying the interval endpoints. -/
theorem mem_exceptionalArguments (f : ℝ → ℝ) (l u : ℝ)
    (Q m : ℕ) (B w L : ℝ) (r : ℚ) :
    r ∈ exceptionalArguments f l u Q m B w L ↔
      r ∈ MahlerLean.sourceFractions l u Q ∧
        HasPolynomialWitness f r m B w L := by
  classical
  simp [exceptionalArguments]

end DiophantineRigidity
