import DiophantineRigidity.BivariateSpecialization

/-!
# Integral Bezout certificates and nonvanishing

An integral Bezout identity with a nonzero constant term prevents
simultaneous vanishing of its coefficient polynomials. This implements
a prerequisite in the proof of the projective-content lemma (4.1).

The construction of the certificate *from coprimality* and its
quantitative height bound remain separate unproved obligations.
-/

noncomputable section

namespace DiophantineRigidity

/-- If finitely many integer polynomials generate an ideal containing
a nonzero integer K, at least one has a nonzero value at any real x. -/
theorem nonzero_coefficient_of_bezout_certificate
    {ι : Type*} (s : Finset ι)
    (F U : ι → Polynomial ℤ) (K : ℤ) (hK : K ≠ 0)
    (hcert : (∑ j ∈ s, U j * F j) = Polynomial.C K)
    (x : ℝ) :
    ∃ j ∈ s, (F j).eval₂ (Int.castRingHom ℝ) x ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hsum :
      ((∑ j ∈ s, U j * F j) : Polynomial ℤ).eval₂
        (Int.castRingHom ℝ) x = 0 := by
    rw [Polynomial.eval₂_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.eval₂_mul]
    simp [hn j hj]
  have hvalue :
      (Polynomial.C K : Polynomial ℤ).eval₂
        (Int.castRingHom ℝ) x = 0 := by
    rw [← hcert]
    exact hsum
  have hKzero : ((Int.castRingHom ℝ) K) = 0 := by
    simpa only [Polynomial.eval₂_C] using hvalue
  have hKreal : ((Int.castRingHom ℝ) K) ≠ 0 := by
    change (K : ℝ) ≠ 0
    exact_mod_cast hK
  exact hKreal hKzero

/-- An integral Bezout certificate for the Y-coefficients ensures
that the denominator-cleared bivariate specialization is nonzero. -/
theorem clearedBivariate_ne_zero_of_bezout
    (F : Polynomial (Polynomial ℤ)) (U : ℕ → Polynomial ℤ)
    (K p q : ℤ) (D : ℕ)
    (hK : K ≠ 0)
    (hcert :
      (∑ j ∈ F.support, U j * F.coeff j) = Polynomial.C K)
    (hdegree : ∀ j, (F.coeff j).natDegree ≤ D)
    (hq : q ≠ 0) :
    clearedBivariate F p q D ≠ 0 := by
  apply clearedBivariate_ne_zero_of_coefficient F p q D hdegree hq
  obtain ⟨j, _hj, hnonzero⟩ :=
    nonzero_coefficient_of_bezout_certificate
      F.support (fun j => F.coeff j) U K hK hcert
        ((p : ℝ) / (q : ℝ))
  exact ⟨j, hnonzero⟩

end DiophantineRigidity
