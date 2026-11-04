import DiophantineRigidity.Witnesses

/-!
# Gate 02: degree monotonicity of polynomial witnesses

An exact, unconditional arithmetic interface. Increasing the degree cutoff
does not discard a witness or an exceptional rational argument. This does
not establish any two-height counting bound.
-/

namespace DiophantineRigidity

/-- A polynomial witness at degree m is also one at every n ≥ m.
This retains exact zeros and all nonprimitive witnesses. -/
theorem HasPolynomialWitness.mono_degree
    {f : ℝ → ℝ} {r : ℚ} {m n : ℕ} {B w L : ℝ}
    (hmn : m ≤ n) (h : HasPolynomialWitness f r m B w L) :
    HasPolynomialWitness f r n B w L := by
  rcases h with ⟨P, hP, hdeg, hlo, hhi, hval⟩
  exact ⟨P, hP, le_trans hdeg hmn, hlo, hhi, hval⟩

/-- Monotonicity of the exceptional *arguments*, not of witness pairs. -/
theorem exceptionalArguments_mono_degree
    (f : ℝ → ℝ) (l u : ℝ) (Q m n : ℕ) (B w L : ℝ)
    (hmn : m ≤ n) :
    exceptionalArguments f l u Q m B w L ⊆
      exceptionalArguments f l u Q n B w L := by
  intro r hr
  rw [mem_exceptionalArguments] at hr ⊢
  exact ⟨hr.1, HasPolynomialWitness.mono_degree hmn hr.2⟩

end DiophantineRigidity
