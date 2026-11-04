import DiophantineRigidity.SelectedIntegerCombination

/-!
# Root avoidance for the actual coefficient polynomial

This removes an artificially supplied finite root set. It instantiates
the selection theorem with the complex roots of A, retaining the
explicit no-common-zero hypothesis and polynomial coefficient bounds.
The remaining critical step is to *derive* no-common-zero from
coprimality over Q[X], not to assume it in the final research theorem.
-/

noncomputable section
namespace DiophantineRigidity

/-- One integer t ≤ kD avoids every actual complex root of A. -/
theorem exists_selected_integer_avoiding_roots
    (A : Polynomial ℂ) (V : ℕ → Polynomial ℤ)
    (k D : ℕ) (hA : A ≠ 0)
    (hdegree : A.natDegree ≤ D)
    (hnoCommon : ∀ ρ : ℂ, A.eval ρ = 0 →
      ∃ j ≤ k, (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      ∀ ρ : ℂ, A.eval ρ = 0 →
        (selectedIntegerCombination V k t).eval₂
          (Int.castRingHom ℂ) ρ ≠ 0 := by
  classical
  let S : Finset ℂ := A.roots.toFinset
  have hcard : S.card ≤ D :=
    (Multiset.toFinset_card_le A.roots).trans
      ((Polynomial.card_roots' A).trans hdegree)
  have hS : ∀ ρ ∈ S, ∃ j ≤ k,
      (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0 := by
    intro ρ hρ
    apply hnoCommon ρ
    have hroot : ρ ∈ A.roots := Multiset.mem_toFinset.mp hρ
    exact (Polynomial.mem_roots hA).mp hroot
  obtain ⟨t, ht, havoids⟩ :=
    exists_selectedIntegerCombination_nonzero_on S V k D hcard hS
  refine ⟨t, ht, ?_⟩
  intro ρ hroot
  apply havoids ρ
  apply Multiset.mem_toFinset.mpr
  exact (Polynomial.mem_roots hA).mpr hroot

/-- The chosen W_t has a coefficient height controlled only by k,D,H. -/
theorem exists_bounded_integer_avoiding_roots
    (A : Polynomial ℂ) (V : ℕ → Polynomial ℤ)
    (k D : ℕ) (H : ℤ)
    (hA : A ≠ 0) (hdegree : A.natDegree ≤ D)
    (hH : 0 ≤ H)
    (hV : ∀ j ≤ k, ∀ i, |(V j).coeff i| ≤ H)
    (hnoCommon : ∀ ρ : ℂ, A.eval ρ = 0 →
      ∃ j ≤ k, (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      (∀ ρ : ℂ, A.eval ρ = 0 →
        (selectedIntegerCombination V k t).eval₂
          (Int.castRingHom ℂ) ρ ≠ 0) ∧
      (∀ i : ℕ,
        |(selectedIntegerCombination V k t).coeff i| ≤
          ((k + 1 : ℕ) : ℤ) *
            (((k * D : ℕ) : ℤ) + 1) ^ k * H) := by
  obtain ⟨t, ht, havoid⟩ :=
    exists_selected_integer_avoiding_roots A V k D hA hdegree hnoCommon
  refine ⟨t, ht, havoid, ?_⟩
  intro i
  exact selectedIntegerCombination_coeff_abs_le_kD V k D t i H ht hH hV

end DiophantineRigidity
