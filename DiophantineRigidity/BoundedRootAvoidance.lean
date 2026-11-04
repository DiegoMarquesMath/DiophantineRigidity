import Mathlib

/-!
# Bounded simultaneous avoidance

At most D distinct forbidden roots and at most k forbidden values
of t per root imply the existence of an integer
0 ≤ t ≤ kD avoiding all constraints.

The proof works over **any characteristic-zero field**, in particular
ℂ, which is the field needed for the projective-content construction
in Lemma 4.1. It is constructive at the finite-set level, without
choosing a transcendental parameter.

A later lemma must build the obstruction polynomial
  B_ρ(T) = Σ_{j=0}^k F_j(ρ) T^j
and prove it is nonzero at each root ρ of the selected degree-D A.
-/

noncomputable section
namespace DiophantineRigidity

/-- A finite family of nonzero polynomials of degree at most k
cannot vanish simultaneously at each of the first k*|s|+1
distinct nonnegative integers. -/
theorem exists_bounded_avoiding_evaluations
    {K : Type*} [Field K] [CharZero K]
    {ι : Type*} (s : Finset ι) (B : ι → Polynomial K) (k : ℕ)
    (hB : ∀ i ∈ s, B i ≠ 0)
    (hdeg : ∀ i ∈ s, (B i).natDegree ≤ k) :
    ∃ t : ℕ, t ≤ s.card * k ∧
      ∀ i ∈ s, (B i).eval (t : K) ≠ 0 := by
  classical
  let P : Polynomial K := ∏ i ∈ s, B i
  have hP : P ≠ 0 := by
    dsimp [P]
    exact Finset.prod_ne_zero_iff.mpr hB
  have hPdeg : P.natDegree ≤ s.card * k := by
    calc
      P.natDegree ≤ ∑ i ∈ s, (B i).natDegree := by
        dsimp [P]
        exact Polynomial.natDegree_prod_le s B
      _ ≤ ∑ _i ∈ s, k :=
        Finset.sum_le_sum (fun i hi => hdeg i hi)
      _ = s.card * k := by simp
  by_contra hnone
  have hvanishes :
      ∀ t : Fin (s.card * k + 1),
        P.eval ((t.val : ℕ) : K) = 0 := by
    intro t
    have hbad :
        ∃ i ∈ s, (B i).eval ((t.val : ℕ) : K) = 0 := by
      by_contra hn
      apply hnone
      refine ⟨t.val, Nat.le_of_lt_succ t.isLt, ?_⟩
      intro i hi hzero
      exact hn ⟨i, hi, hzero⟩
    obtain ⟨i, hi, hzero⟩ := hbad
    change (∏ j ∈ s, B j).eval ((t.val : ℕ) : K) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hi hzero
  have hinj :
      Function.Injective (fun t : Fin (s.card * k + 1) =>
        ((t.val : ℕ) : K)) := by
    intro a b hab
    apply Fin.ext
    exact (Nat.cast_injective hab)
  have hcard :
      P.natDegree < Fintype.card (Fin (s.card * k + 1)) := by
    simpa using lt_of_le_of_lt hPdeg (Nat.lt_succ_self _)
  exact hP
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      P hinj hvanishes hcard)

/-- The precise kD bound in Lemma 4.1, given at most D
nonzero obstruction polynomials, all of degree at most k. -/
theorem exists_avoiding_with_kD_bound
    {K : Type*} [Field K] [CharZero K]
    {ι : Type*} (s : Finset ι) (B : ι → Polynomial K)
    (k D : ℕ) (hcard : s.card ≤ D)
    (hB : ∀ i ∈ s, B i ≠ 0)
    (hdeg : ∀ i ∈ s, (B i).natDegree ≤ k) :
    ∃ t : ℕ, t ≤ k * D ∧
      ∀ i ∈ s, (B i).eval (t : K) ≠ 0 := by
  obtain ⟨t, ht, heval⟩ :=
    exists_bounded_avoiding_evaluations s B k hB hdeg
  refine ⟨t, ?_, heval⟩
  calc
    t ≤ s.card * k := ht
    _ ≤ D * k := Nat.mul_le_mul_right k hcard
    _ = k * D := Nat.mul_comm _ _

end DiophantineRigidity
