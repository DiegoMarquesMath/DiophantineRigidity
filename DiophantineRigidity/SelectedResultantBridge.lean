import DiophantineRigidity.RationalCoefficientCoprimality
import DiophantineRigidity.ResultantBaseChange

/-!
# Selected integral Sylvester resultants from coefficient coprimality

This module joins three independently verified ingredients:
(1) the rational coefficient ideal condition provides a bounded parameter
    t and complex coprimality of A and the selected integer W_t;
(2) exact left degree D ensures Sylvester nonvanishing even when
    the right degree is smaller than its nominal bound e;
(3) base change transfers nonvanishing to the original integer resultant.

The right-degree bound is still an explicit hypothesis on each selected
polynomial. Its derivation from uniform degree bounds on V_j is a separate
routine algebraic interface.
-/

noncomputable section

namespace DiophantineRigidity

/-- A rational coefficient unit-ideal condition supplies one bounded
integer choice t for which the *integer* nominal-degree Sylvester
resultant does not vanish. No resultant nonvanishing is assumed.

We explicitly require the degree of each selected polynomial (after
base change) to be at most e, including possible degree drops. -/
theorem exists_selected_integer_nonzero_resultant
    (A : Polynomial ℤ) (V : ℕ → Polynomial ℤ)
    (k D e : ℕ)
    (hA : A.map (Int.castRingHom ℂ) ≠ 0)
    (hD : (A.map (Int.castRingHom ℂ)).natDegree = D)
    (hspan : rationalCoefficientIdeal
      (A.map (Int.castRingHom ℚ))
      (fun j => (V j).map (Int.castRingHom ℚ)) k = ⊤)
    (hWdeg : ∀ t ≤ k * D,
      ((selectedIntegerCombination V k t).map
        (Int.castRingHom ℂ)).natDegree ≤ e) :
    ∃ t : ℕ, t ≤ k * D ∧
      Polynomial.resultant A (selectedIntegerCombination V k t) D e ≠ 0 := by
  obtain ⟨t, ht, hcop⟩ :=
    exists_selected_integer_coprime_of_rationalCoefficientIdeal
      A V k D hA (le_of_eq hD) hspan
  have hcomplex :
      Polynomial.resultant (A.map (Int.castRingHom ℂ))
        ((selectedIntegerCombination V k t).map
          (Int.castRingHom ℂ)) D e ≠ 0 :=
    resultant_ne_zero_of_coprime_exact_left
      (A.map (Int.castRingHom ℂ))
      ((selectedIntegerCombination V k t).map
        (Int.castRingHom ℂ))
      D e hA hD (hWdeg t ht) hcop
  exact ⟨t, ht,
    resultant_integer_ne_zero_of_complex
      A (selectedIntegerCombination V k t) D e hcomplex⟩

/-- The same parameter simultaneously gives the nonzero integer
resultant and the explicit uniform coefficient bound on W_t.

The height constant depends on k,D, but not on the coefficients
of A,V or the selected parameter. -/
theorem exists_selected_integer_nonzero_resultant_with_height
    (A : Polynomial ℤ) (V : ℕ → Polynomial ℤ)
    (k D e : ℕ) (H : ℤ)
    (hA : A.map (Int.castRingHom ℂ) ≠ 0)
    (hD : (A.map (Int.castRingHom ℂ)).natDegree = D)
    (hspan : rationalCoefficientIdeal
      (A.map (Int.castRingHom ℚ))
      (fun j => (V j).map (Int.castRingHom ℚ)) k = ⊤)
    (hWdeg : ∀ t ≤ k * D,
      ((selectedIntegerCombination V k t).map
        (Int.castRingHom ℂ)).natDegree ≤ e)
    (hH : 0 ≤ H)
    (hV : ∀ j ≤ k, ∀ i, |(V j).coeff i| ≤ H) :
    ∃ t : ℕ, t ≤ k * D ∧
      Polynomial.resultant A (selectedIntegerCombination V k t) D e ≠ 0 ∧
      ∀ i : ℕ, |(selectedIntegerCombination V k t).coeff i| ≤
        ((k + 1 : ℕ) : ℤ) *
          (((k * D : ℕ) : ℤ) + 1) ^ k * H := by
  obtain ⟨t, ht, hres⟩ :=
    exists_selected_integer_nonzero_resultant
      A V k D e hA hD hspan hWdeg
  exact ⟨t, ht, hres, fun i =>
    selectedIntegerCombination_coeff_abs_le_kD
      V k D t i H ht hH hV⟩

end DiophantineRigidity
