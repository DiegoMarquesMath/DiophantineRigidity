import DiophantineRigidity.ComplexCoprimality
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Kernel rigidity of the exact-degree Sylvester map

If A,W∈ℂ[X] are coprime and deg A = D, then no nontrivial
low-degree pair U,V can satisfy A U+W V=0 with deg V<D.
This is precisely the injectivity mechanism in the Sylvester
determinant argument. The separate determinant bridge is needed
to infer a nonzero nominal-degree integer resultant.

No theorem-equivalent nonvanishing resultant is assumed here.
-/

noncomputable section
namespace DiophantineRigidity

/-- The kernel obstruction for the Sylvester map vanishes by Euclid's
lemma for coprime polynomials and the strict degree inequality. -/
theorem sylvester_kernel_zero_of_coprime
    (A W U V : Polynomial ℂ) (D : ℕ)
    (hA : A ≠ 0) (hAdeg : A.natDegree = D)
    (hcop : IsCoprime A W)
    (hV : V.degree < (D : WithBot ℕ))
    (hrel : A * U + W * V = 0) :
    U = 0 ∧ V = 0 := by
  have hdiv : A ∣ W * V := by
    have hv : W * V = -(A * U) := by
      calc
        W * V = (A * U + W * V) - A * U := by ring
        _ = -(A * U) := by rw [hrel]; ring
    rw [hv]
    exact ⟨-U, by ring⟩
  have hAdvd : A ∣ V := hcop.dvd_of_dvd_mul_left hdiv
  have hVzero : V = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_degree_lt hAdvd
    have hdeg : A.degree = (D : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hA, hAdeg]
    rw [hdeg]
    exact hV
  have hUzero : U = 0 := by
    have hmul : A * U = 0 := by simpa [hVzero] using hrel
    exact (mul_eq_zero.mp hmul).resolve_left hA
  exact ⟨hUzero, hVzero⟩

/-- A bounded selected integer polynomial has no nontrivial
Sylvester relation of degrees (e,D), whenever A has exact degree D.
The bound on deg U is retained for compatibility with the Sylvester
matrix, although algebraic rigidity already follows from deg V<D. -/
theorem exists_selected_integer_sylvester_kernel_zero
    (A : Polynomial ℂ) (V : ℕ → Polynomial ℤ)
    (k D e : ℕ)
    (hA : A ≠ 0) (hAdeg : A.natDegree = D)
    (hnoCommon : ∀ ρ : ℂ, A.eval ρ = 0 →
      ∃ j ≤ k, (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      ∀ (U T : Polynomial ℂ),
        U.degree < (e : WithBot ℕ) →
        T.degree < (D : WithBot ℕ) →
        A * U +
          (selectedIntegerCombination V k t).map (Int.castRingHom ℂ) * T = 0 →
        U = 0 ∧ T = 0 := by
  obtain ⟨t, ht, hcop⟩ :=
    exists_selected_integer_coprime_complex
      A V k D hA (le_of_eq hAdeg) hnoCommon
  refine ⟨t, ht, ?_⟩
  intro U T _hU hT hrel
  exact sylvester_kernel_zero_of_coprime A
    ((selectedIntegerCombination V k t).map (Int.castRingHom ℂ))
    U T D hA hAdeg hcop hT hrel

end DiophantineRigidity
