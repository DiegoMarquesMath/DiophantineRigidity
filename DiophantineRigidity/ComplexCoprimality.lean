import DiophantineRigidity.PolynomialRootAvoidance
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Coprimality of the selected polynomial

The selected integer combination has no roots in common with A.
Over ℂ this implies that the polynomials are coprime.

The nonzero integral Sylvester determinant at the nominal degree
parameters is not inferred here, and remains open.
-/

noncomputable section
namespace DiophantineRigidity

theorem complex_isCoprime_of_no_common_root
    (A W : Polynomial ℂ)
    (h : ∀ ρ : ℂ, A.eval ρ = 0 → W.eval ρ ≠ 0) :
    IsCoprime A W := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ A W).2
  intro ρ
  have heval (P : Polynomial ℂ) :
      Polynomial.aeval ρ P = P.eval ρ := by
    simp [Polynomial.aeval_def]
  by_cases hz : A.eval ρ = 0
  · right
    simpa only [heval] using h ρ hz
  · left
    simpa only [heval] using hz

theorem exists_selected_integer_coprime_complex
    (A : Polynomial ℂ) (V : ℕ → Polynomial ℤ)
    (k D : ℕ) (hA : A ≠ 0)
    (hdegree : A.natDegree ≤ D)
    (hnoCommon : ∀ ρ : ℂ, A.eval ρ = 0 →
      ∃ j ≤ k, (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      IsCoprime A
        ((selectedIntegerCombination V k t).map
          (Int.castRingHom ℂ)) := by
  obtain ⟨t, ht, havoids⟩ :=
    exists_selected_integer_avoiding_roots
      A V k D hA hdegree hnoCommon
  refine ⟨t, ht, ?_⟩
  apply complex_isCoprime_of_no_common_root
  intro ρ hroot
  have hw := havoids ρ hroot
  simpa only [Polynomial.eval_map] using hw

end DiophantineRigidity
