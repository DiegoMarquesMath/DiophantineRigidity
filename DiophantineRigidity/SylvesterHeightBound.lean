import DiophantineRigidity.SylvesterCertificates
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Effective height of integral Sylvester certificates

The present module gives the *quantitative* determinant estimate
required in the proof of the projective-content lemma.

The entries of Syl(A,W;D,e) are coefficients of A or W or zero.
Consequently, if all these coefficients have modulus at most H,
the integral resultant has modulus at most (D+e)! H^(D+e).

When det Syl ≠ 0, the previous adjugate construction produces
an explicit nonzero integer K within this same bound.

A later formalization must derive the determinant's nonvanishing
from polynomial coprimality and construct an appropriate W_t.
-/

noncomputable section
namespace DiophantineRigidity

/-- The basic integer-matrix determinant inequality, using
the absolute-value formalism in the pinned mathlib. -/
theorem integer_matrix_det_abs_le
    (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ) (H : ℤ)
    (hentry : ∀ i j, |M i j| ≤ H) :
    |M.det| ≤ N.factorial • H ^ N := by
  simpa only [Fintype.card_fin] using
    (Matrix.det_le (A := M)
      (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
      (x := H) hentry)

/-- Every entry of the Sylvester matrix is either zero, an
A-coefficient, or a W-coefficient. The result is valid even when
the nominal degree bounds exceed the actual degrees. -/
theorem sylvester_entries_abs_le
    (A W : Polynomial ℤ) (D e : ℕ) (H : ℤ)
    (hH : 0 ≤ H)
    (hA : ∀ j, |A.coeff j| ≤ H)
    (hW : ∀ j, |W.coeff j| ≤ H) :
    ∀ i j, |(Polynomial.sylvester A W D e) i j| ≤ H := by
  intro i j
  refine Fin.addCases ?_ ?_ j
  · intro j
    change
      |(if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + D)
        then A.coeff ((i : ℕ) - j) else 0)| ≤ H
    split_ifs
    · exact hA _
    · simpa using hH
  · intro j
    change
      |(if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e)
        then W.coeff ((i : ℕ) - j) else 0)| ≤ H
    split_ifs
    · exact hW _
    · simpa using hH

/-- Quantitative bound for the integral Sylvester determinant.
No coprimality is required for the inequality itself. -/
theorem sylvester_resultant_abs_le
    (A W : Polynomial ℤ) (D e : ℕ) (H : ℤ)
    (hH : 0 ≤ H)
    (hA : ∀ j, |A.coeff j| ≤ H)
    (hW : ∀ j, |W.coeff j| ≤ H) :
    |Polynomial.resultant A W D e| ≤
      (e + D).factorial • H ^ (e + D) := by
  change |(Polynomial.sylvester A W D e).det| ≤ _
  exact integer_matrix_det_abs_le (e + D)
    (Polynomial.sylvester A W D e) H
    (sylvester_entries_abs_le A W D e H hH hA hW)

/-- The first quantitative integral Bezout theorem in the project:
a nonzero Sylvester determinant yields coefficients U,V and a
nonzero integer K with degree control and explicit height bound.

The hypothesis hdet is a NONZERO RESULTANT condition, not a
Bézout certificate. Replacing it by coprimality is a future lemma. -/
theorem exists_bounded_integral_sylvester_certificate
    (A W : Polynomial ℤ) (D e : ℕ) (H : ℤ)
    (hAdeg : A.natDegree ≤ D) (hWdeg : W.natDegree ≤ e)
    (hsize : D ≠ 0 ∨ e ≠ 0)
    (hdet : Polynomial.resultant A W D e ≠ 0)
    (hH : 0 ≤ H)
    (hA : ∀ j, |A.coeff j| ≤ H)
    (hW : ∀ j, |W.coeff j| ≤ H) :
    ∃ (U V : Polynomial ℤ) (K : ℤ),
      K ≠ 0 ∧
      |K| ≤ (e + D).factorial • H ^ (e + D) ∧
      U.degree < (e : WithBot ℕ) ∧
      V.degree < (D : WithBot ℕ) ∧
      A * U + W * V = Polynomial.C K := by
  obtain ⟨U, V, hU, hV, hcert⟩ :=
    exists_integral_sylvester_certificate A W D e hAdeg hWdeg hsize
  exact ⟨U, V, Polynomial.resultant A W D e,
    hdet, sylvester_resultant_abs_le A W D e H hH hA hW,
    hU, hV, hcert⟩

end DiophantineRigidity
