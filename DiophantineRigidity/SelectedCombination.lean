import DiophantineRigidity.BoundedRootAvoidance

/-!
# Selecting one bounded parameter for a polynomial combination

For a finite set S of complex points and a family V_j(X), assume
that at each ρ∈S some V_j(ρ) with 0≤j≤k is nonzero.

We construct a single integer 0≤t≤kD such that the genuine
polynomial W_t(X)=Σ_{j=0}^k t^j V_j(X) does not vanish at any ρ∈S,
provided |S|≤D.

The full Lemma 4.1 next has to instantiate S as the root set of A,
with |S|≤deg A=D, and produce this non-common-vanishing assumption
from the coefficient coprimality in ℚ[X].
-/

noncomputable section
namespace DiophantineRigidity

/-- A degree-k polynomial in the auxiliary parameter T obtained by
evaluating each V_j at a fixed complex number ρ. -/
def obstructionPolynomial (V : ℕ → Polynomial ℂ)
    (k : ℕ) (ρ : ℂ) : Polynomial ℂ :=
  Polynomial.ofFinsupp
    (Finsupp.onFinset (Finset.range (k + 1))
      (fun j => if j < k + 1 then (V j).eval ρ else 0)
      (by
        intro j hj
        by_contra hn
        have hn' : ¬ j < k + 1 := by
          simpa using hn
        simp [hn'] at hj))

theorem obstructionPolynomial_coeff
    (V : ℕ → Polynomial ℂ) (k : ℕ) (ρ : ℂ) (j : ℕ) :
    (obstructionPolynomial V k ρ).coeff j =
      if j < k + 1 then (V j).eval ρ else 0 := by
  rfl

/-- The obstruction polynomial always has parameter degree ≤k. -/
theorem obstructionPolynomial_natDegree_le
    (V : ℕ → Polynomial ℂ) (k : ℕ) (ρ : ℂ) :
    (obstructionPolynomial V k ρ).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_degree_le,
      Polynomial.degree_le_iff_coeff_zero]
  intro j hj
  have hj' : k < j := by exact_mod_cast hj
  have hnot : ¬ j < k + 1 := by omega
  simp [obstructionPolynomial_coeff, hnot]

/-- Any nonzero V_j(ρ) gives a nonzero obstruction polynomial. -/
theorem obstructionPolynomial_ne_zero
    (V : ℕ → Polynomial ℂ) (k : ℕ) (ρ : ℂ)
    (h : ∃ j ≤ k, (V j).eval ρ ≠ 0) :
    obstructionPolynomial V k ρ ≠ 0 := by
  obtain ⟨j, hj, hj0⟩ := h
  intro hz
  have hzj := congrArg (fun P : Polynomial ℂ => P.coeff j) hz
  have hlt : j < k + 1 := Nat.lt_succ_iff.mpr hj
  have hzero : (V j).eval ρ = 0 := by
    simpa [obstructionPolynomial_coeff, hlt] using hzj
  exact hj0 hzero

/-- Evaluation of the obstruction polynomial agrees with the
coefficient combination at the parameter t. -/
theorem obstructionPolynomial_eval
    (V : ℕ → Polynomial ℂ) (k : ℕ) (ρ t : ℂ) :
    (obstructionPolynomial V k ρ).eval t =
      ∑ j ∈ Finset.range (k + 1), (V j).eval ρ * t ^ j := by
  have hdeg :
      (obstructionPolynomial V k ρ).natDegree < k + 1 :=
    Nat.lt_succ_of_le (obstructionPolynomial_natDegree_le V k ρ)
  rw [Polynomial.eval_eq_sum_range' hdeg t]
  apply Finset.sum_congr rfl
  intro j hj
  rw [obstructionPolynomial_coeff, if_pos (Finset.mem_range.mp hj)]

/-- Actual integer-parameter polynomial W_t(X). -/
def selectedCombination (V : ℕ → Polynomial ℂ)
    (k t : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k + 1),
    Polynomial.C ((t : ℂ) ^ j) * V j

theorem selectedCombination_eval
    (V : ℕ → Polynomial ℂ) (k t : ℕ) (ρ : ℂ) :
    (selectedCombination V k t).eval ρ =
      ∑ j ∈ Finset.range (k + 1),
        (V j).eval ρ * (t : ℂ) ^ j := by
  unfold selectedCombination
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_C_mul]
  ring

/-- A bounded integer parameter simultaneously avoids all complex
points in S for the *actual* polynomial W_t. -/
theorem exists_selectedCombination_nonzero_on
    (S : Finset ℂ) (V : ℕ → Polynomial ℂ)
    (k D : ℕ) (hcard : S.card ≤ D)
    (hnoCommon : ∀ ρ ∈ S, ∃ j ≤ k, (V j).eval ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      ∀ ρ ∈ S, (selectedCombination V k t).eval ρ ≠ 0 := by
  let B : ℂ → Polynomial ℂ := obstructionPolynomial V k
  have hB : ∀ ρ ∈ S, B ρ ≠ 0 := by
    intro ρ hρ
    exact obstructionPolynomial_ne_zero V k ρ (hnoCommon ρ hρ)
  have hdeg : ∀ ρ ∈ S, (B ρ).natDegree ≤ k := by
    intro ρ _
    exact obstructionPolynomial_natDegree_le V k ρ
  obtain ⟨t, ht, havoid⟩ :=
    exists_avoiding_with_kD_bound S B k D hcard hB hdeg
  refine ⟨t, ht, ?_⟩
  intro ρ hρ
  have hh := havoid ρ hρ
  have heq :
      (B ρ).eval (t : ℂ) = (selectedCombination V k t).eval ρ := by
    rw [selectedCombination_eval, obstructionPolynomial_eval]
  rw [heq] at hh
  exact hh

end DiophantineRigidity
