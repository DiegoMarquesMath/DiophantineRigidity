/-
Adapted from the Sylvester-map strategy developed in mathlib
(Anne Baanen and Kenny Lau; Apache 2.0 license).
The Lean 4.24.0 pinned version uses the *n+m* column convention
and does not yet provide the requisite adjugate certificate API.
-/

import DiophantineRigidity.SylvesterKernel
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Integral Sylvester certificates

This module constructs integer Bezout certificates from the
**nonvanishing of a Sylvester determinant**. Unlike the preceding
conditional specialization lemmas, the coefficient polynomials U,V
are obtained directly from a matrix adjugate, not assumed.

The critical next obligation is proving this determinant is nonzero
from coprimality and bounding its absolute value by O(H^(m+n)).
-/

open Polynomial
open scoped Polynomial

noncomputable section

namespace DiophantineRigidity

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- For deg f≤m and deg g≤n, the Sylvester linear map of pairs
U (degree<n), V (degree<m) into fU+gV. -/
private def sylvesterLinear
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    R[X]_n × R[X]_m →ₗ[R] R[X]_(n + m) where
  toFun uv := ⟨f * uv.1 + g * uv.2, by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := uv
    rw [Polynomial.mem_degreeLT]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · by_cases hf0 : f = 0
      · simp [hf0]
        exact ⟨WithBot.bot_lt_coe n, WithBot.bot_lt_coe m⟩
      exact (degree_mul_le _ _).trans_lt
        ((WithBot.add_lt_add_of_le_of_lt (by simpa)
          (degree_le_of_natDegree_le hf) ((Polynomial.mem_degreeLT).mp hu)).trans_eq
          (add_comm _ _))
    · by_cases hg0 : g = 0
      · simp [hg0]
        exact ⟨WithBot.bot_lt_coe n, WithBot.bot_lt_coe m⟩
      exact (degree_mul_le _ _).trans_lt
        (WithBot.add_lt_add_of_le_of_lt (by simpa)
          (degree_le_of_natDegree_le hg) ((Polynomial.mem_degreeLT).mp hv))⟩
  map_add' _ _ := by ext1; dsimp; ring
  map_smul' _ _ := by ext1; simp

/-- The matrix of the linear map agrees with the pinned mathlib
Sylvester matrix. On v4.24.0 its first n columns are shifts of f. -/
private lemma sylvesterLinear_toMatrix
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterLinear f g hf hg).toMatrix
      ((degreeLT.basis R n).prod (degreeLT.basis R m))
      (degreeLT.basis R (n + m)) =
    (Polynomial.sylvester f g m n).reindex (.refl _) finSumFinEquiv.symm := by
  ext i (j | j)
  · suffices (if j.1 ≤ i then f.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + m then f.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvesterLinear,
          Polynomial.sylvester, Polynomial.coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · suffices (if j.1 ≤ i then g.coeff (i - j) else 0) =
      if j ≤ i.1 ∧ ↑i ≤ j + n then g.coeff (i - j) else 0 by
        simpa [LinearMap.toMatrix_apply, sylvesterLinear,
          Polynomial.sylvester, Polynomial.coeff_mul_X_pow']
    rw [ite_and]
    split_ifs with h₁ h₂ <;> try rfl
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma sylvesterLinear_matrix
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (sylvesterLinear f g hf hg).toMatrix
      (degreeLT.basisProd R n m) (degreeLT.basis R (n + m)) =
        Polynomial.sylvester f g m n := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simpa [degreeLT.basisProd, LinearMap.toMatrix_apply] using
    congr($(sylvesterLinear_toMatrix f g hf hg) i j)

/-- Integral adjugate of the Sylvester matrix, interpreted as a map
back to bounded-degree polynomial pairs. -/
private def adjSylvesterLinear (f g : R[X]) (m n : ℕ) :
    R[X]_(n + m) →ₗ[R] R[X]_n × R[X]_m :=
  (Polynomial.sylvester f g m n).adjugate.toLin
    (degreeLT.basis R (n + m)) (degreeLT.basisProd R n m)

private theorem sylvesterLinear_comp_adj
    (f g : R[X]) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    sylvesterLinear f g hf hg ∘ₗ adjSylvesterLinear f g m n =
      Polynomial.resultant f g m n • LinearMap.id := by
  let b₁ := degreeLT.basisProd R n m
  let b₂ := degreeLT.basis R (n + m)
  have h := congr(Matrix.toLin b₂ b₂
    $(((sylvesterLinear f g hf hg).toMatrix b₁ b₂).mul_adjugate))
  rwa [Matrix.toLin_mul b₂ b₁ b₂, Matrix.toLin_toMatrix, map_smul,
    sylvesterLinear_matrix, Matrix.toLin_one, ← Polynomial.resultant] at h

/-- The integral Sylvester Bezout identity, *with both coefficient
polynomials explicitly constructed*. The upper degree bounds are
arbitrary; they need not be the exact degrees. This identity remains
valid when the determinant vanishes, although the subsequent content
argument requires it to be nonzero. -/
theorem exists_integral_sylvester_certificate
    (f g : Polynomial ℤ) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hsize : m ≠ 0 ∨ n ≠ 0) :
    ∃ U V : Polynomial ℤ,
      U.degree < (n : WithBot ℕ) ∧
      V.degree < (m : WithBot ℕ) ∧
      f * U + g * V = Polynomial.C (Polynomial.resultant f g m n) := by
  let e : (ℤ[X]_(n + m)) :=
    ⟨1, by
      simpa [Polynomial.mem_degreeLT, ← Nat.cast_add, Nat.pos_iff_ne_zero,
        not_and_or, -not_and] using hsize.symm⟩
  let uv := adjSylvesterLinear f g m n e
  have hproof :
      ((sylvesterLinear f g hf hg uv)).1 =
        ((Polynomial.resultant f g m n : ℤ) • e : ℤ[X]) := by
    have hx := congrArg (fun T : ℤ[X]_(n + m) →ₗ[ℤ] ℤ[X]_(n + m) =>
      ((T e : ℤ[X]_(n + m)) : ℤ[X]))
      (sylvesterLinear_comp_adj f g hf hg)
    simpa [LinearMap.comp_apply, uv, e] using hx
  exact ⟨uv.1, uv.2,
    (Polynomial.mem_degreeLT).mp uv.1.2,
    (Polynomial.mem_degreeLT).mp uv.2.2,
    by simpa [sylvesterLinear, Algebra.smul_def, e] using hproof⟩

/-- A nonzero integral Sylvester determinant yields a nonzero constant
in a concrete integral Bezout identity. No rational/integer certificate
is assumed in the premises. -/
theorem exists_nonzero_integral_sylvester_certificate
    (f g : Polynomial ℤ) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hsize : m ≠ 0 ∨ n ≠ 0)
    (hdet : Polynomial.resultant f g m n ≠ 0) :
    ∃ (U V : Polynomial ℤ) (K : ℤ),
      K ≠ 0 ∧ U.degree < (n : WithBot ℕ) ∧
      V.degree < (m : WithBot ℕ) ∧
      f * U + g * V = Polynomial.C K := by
  obtain ⟨U, V, hU, hV, hcert⟩ :=
    exists_integral_sylvester_certificate f g m n hf hg hsize
  exact ⟨U, V, Polynomial.resultant f g m n, hdet, hU, hV, hcert⟩

/-- Coprimality over ℂ[X] gives a nonzero Sylvester resultant
with exact LEFT degree D but merely an upper RIGHT degree e.
The proof identifies the Sylvester matrix with the linear map
(U,V) ↦ A U + W V and uses its zero kernel. -/
theorem resultant_ne_zero_of_coprime_exact_left
    (A W : Polynomial ℂ) (D e : ℕ)
    (hA : A ≠ 0) (hD : A.natDegree = D)
    (hW : W.natDegree ≤ e)
    (hcop : IsCoprime A W) :
    Polynomial.resultant A W D e ≠ 0 := by
  classical
  let L : ℂ[X]_e × ℂ[X]_D →ₗ[ℂ] ℂ[X]_(e + D) :=
    sylvesterLinear A W (le_of_eq hD) hW
  let b₁ := degreeLT.basisProd ℂ e D
  let b₂ := degreeLT.basis ℂ (e + D)
  have hinj : Function.Injective L := by
    intro u v huv
    have hsub : L (u - v) = 0 := by
      simp [map_sub, huv]
    have hpoly :
        A * ((u - v).1 : ℂ[X]) + W * ((u - v).2 : ℂ[X]) = 0 := by
      have hz := congrArg (fun z : ℂ[X]_(e + D) => (z : ℂ[X])) hsub
      change A * ((u - v).1 : ℂ[X]) + W * ((u - v).2 : ℂ[X]) = 0 at hz
      exact hz
    have hVdeg : ((u - v).2 : ℂ[X]).degree < (D : WithBot ℕ) :=
      (Polynomial.mem_degreeLT).mp (u - v).2.2
    obtain ⟨hu, hv⟩ :=
      sylvester_kernel_zero_of_coprime A W
        ((u - v).1 : ℂ[X]) ((u - v).2 : ℂ[X])
        D hA hD hcop hVdeg hpoly
    have hdiff : u - v = 0 := by
      apply Prod.ext
      · exact Subtype.ext hu
      · exact Subtype.ext hv
    exact sub_eq_zero.mp hdiff
  have hmatrix :
      L.toMatrix b₁ b₂ = Polynomial.sylvester A W D e := by
    exact sylvesterLinear_matrix A W (le_of_eq hD) hW
  intro hdet
  have hdet' : (L.toMatrix b₁ b₂).det = 0 := by
    simpa only [hmatrix] using hdet
  obtain ⟨v, hv, hmul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff).mpr hdet'
  let x : ℂ[X]_e × ℂ[X]_D := b₁.equivFun.symm v
  have hrepr : (fun i => b₁.repr x i) = v := by
    simpa only [Basis.equivFun_apply] using
      (b₁.equivFun.apply_symm_apply v)
  have hm := LinearMap.toMatrix_mulVec_repr b₁ b₂ L x
  rw [hrepr, hmul] at hm
  have hLx : L x = 0 := by
    apply b₂.equivFun.injective
    simpa only [Basis.equivFun_apply, map_zero] using hm.symm
  have hx : x = 0 := hinj (by simpa using hLx)
  have hvzero : v = 0 := by
    have hh := congrArg b₁.equivFun hx
    simpa [x] using hh
  exact hv hvzero

end DiophantineRigidity
