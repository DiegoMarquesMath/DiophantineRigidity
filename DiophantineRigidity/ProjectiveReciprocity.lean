import DiophantineRigidity.ProjectiveBezoutBridge
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Reciprocal projective chart

The two charts of projective specialization are given by F_j(X)
and reflect D F_j(X) = X^D F_j(1/X). Unlike ordinary reversal, the
reflection uses the SAME degree bound D for every coefficient.

We prove their integer-cleared specializations coincide after
interchanging p and q, then combine both supplied integral Bezout
certificates to bound the content by a constant independent of p,q.

This closes the elementary algebraic cancellation step of Lemma 4.1.
Constructing the certificates with the sharp height bound, and
the nonarchimedean counting lemma, remain open.
-/

noncomputable section

namespace DiophantineRigidity

/-- Reflection at an upper degree D does not increase the degree. -/
theorem reflect_natDegree_le (P : Polynomial ℤ) (D : ℕ)
    (hD : P.natDegree ≤ D) :
    (Polynomial.reflect D P).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_degree_le,
      Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hn]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hD hn)

/-- The two homogenized integer evaluations agree:
q^D P(p/q) = p^D (reflect D P)(q/p).
We assume nonzero coordinates, leaving p=0 (at most one reduced
rational argument) for the separate endpoint case in Lemma 4.1. -/
theorem clearedEvaluation_reflect
    (P : Polynomial ℤ) (p q : ℤ) (D : ℕ)
    (hD : P.natDegree ≤ D)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    clearedEvaluation P p q D =
      clearedEvaluation (Polynomial.reflect D P) q p D := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  let x : ℝ := (p : ℝ) / (q : ℝ)
  have hx : x ≠ 0 := div_ne_zero hpR hqR
  letI : Invertible x := invertibleOfNonzero hx
  have hkey :
      (Polynomial.reflect D P).eval₂ (Int.castRingHom ℝ) (⅟x) *
          x ^ D =
        P.eval₂ (Int.castRingHom ℝ) x :=
    Polynomial.eval₂_reflect_mul_pow (Int.castRingHom ℝ) x D P hD
  have hqx : (q : ℝ) * x = (p : ℝ) := by
    dsimp [x]
    field_simp [hqR]
  have hpow : (q : ℝ) ^ D * x ^ D = (p : ℝ) ^ D := by
    rw [← mul_pow, hqx]
  have hinv : ⅟x = (q : ℝ) / (p : ℝ) := by
    rw [invOf_eq_inv]
    dsimp [x]
    field_simp [hpR, hqR]
  have hvalue :
      (q : ℝ) ^ D * P.eval₂ (Int.castRingHom ℝ) x =
        (p : ℝ) ^ D *
          (Polynomial.reflect D P).eval₂ (Int.castRingHom ℝ)
            ((q : ℝ) / (p : ℝ)) := by
    calc
      _ = (q : ℝ) ^ D *
            ((Polynomial.reflect D P).eval₂
              (Int.castRingHom ℝ) (⅟x) * x ^ D) := by rw [hkey]
      _ = ((q : ℝ) ^ D * x ^ D) *
            (Polynomial.reflect D P).eval₂ (Int.castRingHom ℝ) (⅟x) := by ring
      _ = (p : ℝ) ^ D *
            (Polynomial.reflect D P).eval₂
              (Int.castRingHom ℝ) ((q : ℝ) / (p : ℝ)) := by rw [hpow, hinv]
  have hreal :
      (clearedEvaluation P p q D : ℝ) =
        (clearedEvaluation (Polynomial.reflect D P) q p D : ℝ) := by
    rw [clearedEvaluation_spec P p q D hD hq,
        clearedEvaluation_spec (Polynomial.reflect D P) q p D
          (reflect_natDegree_le P D hD) hp]
    change (q : ℝ) ^ D * P.eval₂ (Int.castRingHom ℝ) x =
      (p : ℝ) ^ D *
        (Polynomial.reflect D P).eval₂ (Int.castRingHom ℝ)
          ((q : ℝ) / (p : ℝ))
    exact hvalue
  exact_mod_cast hreal

/-- Reflect every X-coefficient of F(X,Y) at the same X-degree D. -/
def reflectedBivariate (F : Polynomial (Polynomial ℤ)) (D : ℕ) :
    Polynomial (Polynomial ℤ) :=
  Polynomial.ofFinsupp
    (Finsupp.onFinset F.support
      (fun j => Polynomial.reflect D (F.coeff j))
      (by
        intro j hj
        by_contra hn
        have hz : F.coeff j = 0 :=
          Polynomial.notMem_support_iff.mp hn
        exact hj (by simp [hz])))

/-- The reflected Y-coefficients are exactly the reflected X-polynomials. -/
theorem reflectedBivariate_coeff
    (F : Polynomial (Polynomial ℤ)) (D j : ℕ) :
    (reflectedBivariate F D).coeff j =
      Polynomial.reflect D (F.coeff j) := by
  rfl

/-- The two *integer* specializations are identical, including all
coefficient zeros and degree drops in Y. -/
theorem clearedBivariate_reflection
    (F : Polynomial (Polynomial ℤ)) (p q : ℤ) (D : ℕ)
    (hF : ∀ j, (F.coeff j).natDegree ≤ D)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    clearedBivariate F p q D =
      clearedBivariate (reflectedBivariate F D) q p D := by
  apply Polynomial.ext
  intro j
  rw [clearedBivariate_coeff, clearedBivariate_coeff,
      reflectedBivariate_coeff]
  exact clearedEvaluation_reflect (F.coeff j) p q D (hF j) hp hq

/-- The content of one specialization is bounded by the product
of the two chart constants. Unlike an abstract cancellation lemma,
this uses the actual reflected coefficient family.

The integral Bezout identities and their degree bounds are hypotheses;
their existence and quantitative construction remain open. -/
theorem integerContent_dvd_product_of_two_Bezout_charts
    (F : Polynomial (Polynomial ℤ))
    (U V : ℕ → Polynomial ℤ)
    (K₁ K₂ p q : ℤ) (D E₁ E₂ : ℕ)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : Nat.Coprime p.natAbs q.natAbs)
    (hF : ∀ j, (F.coeff j).natDegree ≤ D)
    (hU : ∀ j ∈ F.support, (U j).natDegree ≤ E₁)
    (hV : ∀ j ∈ (reflectedBivariate F D).support,
      (V j).natDegree ≤ E₂)
    (hcert₁ :
      (∑ j ∈ F.support, U j * F.coeff j) = Polynomial.C K₁)
    (hcert₂ :
      (∑ j ∈ (reflectedBivariate F D).support,
        V j * (reflectedBivariate F D).coeff j) = Polynomial.C K₂) :
    integerContent (clearedBivariate F p q D) ∣ K₁.natAbs * K₂.natAbs := by
  let g := integerContent (clearedBivariate F p q D)
  have h₁ : (g : ℤ) ∣ K₁ * q ^ (D + E₁) :=
    integerContent_dvd_Bezout_chart
      F U K₁ p q D E₁ hq (by intro j _; exact hF j) hU hcert₁
  have hFref :
      ∀ j ∈ (reflectedBivariate F D).support,
        ((reflectedBivariate F D).coeff j).natDegree ≤ D := by
    intro j _
    rw [reflectedBivariate_coeff]
    exact reflect_natDegree_le (F.coeff j) D (hF j)
  have h₂ref :
      ((integerContent
          (clearedBivariate (reflectedBivariate F D) q p D) : ℕ) : ℤ) ∣
        K₂ * p ^ (D + E₂) :=
    integerContent_dvd_Bezout_chart
      (reflectedBivariate F D) V K₂ q p D E₂ hp hFref hV hcert₂
  have h₂ : (g : ℤ) ∣ K₂ * p ^ (D + E₂) := by
    simpa only [g, clearedBivariate_reflection F p q D hF hp hq] using h₂ref
  have hn₁ : g ∣ K₁.natAbs * q.natAbs ^ (D + E₁) := by
    have h := (Int.natAbs_dvd_natAbs).mpr h₁
    simpa only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] using h
  have hn₂ : g ∣ K₂.natAbs * p.natAbs ^ (D + E₂) := by
    have h := (Int.natAbs_dvd_natAbs).mpr h₂
    simpa only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow] using h
  exact twoChart_dvd_product g K₁.natAbs K₂.natAbs
    q.natAbs p.natAbs (D + E₁) (D + E₂) hpq.symm hn₁ hn₂


/-- A quantitative form of the two-chart content divisibility theorem.
If both supplied integral certificate constants are nonzero, the
integer content is bounded independently of the coprime coordinates p,q.
This holds even if the specialized polynomial is zero: in that case
the hypotheses force a contradiction, rather than silently excluding it. -/
theorem integerContent_le_product_of_two_Bezout_charts
    (F : Polynomial (Polynomial ℤ))
    (U V : ℕ → Polynomial ℤ)
    (K₁ K₂ p q : ℤ) (D E₁ E₂ : ℕ)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : Nat.Coprime p.natAbs q.natAbs)
    (hF : ∀ j, (F.coeff j).natDegree ≤ D)
    (hU : ∀ j ∈ F.support, (U j).natDegree ≤ E₁)
    (hV : ∀ j ∈ (reflectedBivariate F D).support,
      (V j).natDegree ≤ E₂)
    (hcert₁ :
      (∑ j ∈ F.support, U j * F.coeff j) = Polynomial.C K₁)
    (hcert₂ :
      (∑ j ∈ (reflectedBivariate F D).support,
        V j * (reflectedBivariate F D).coeff j) = Polynomial.C K₂)
    (hK₁ : K₁ ≠ 0) (hK₂ : K₂ ≠ 0) :
    integerContent (clearedBivariate F p q D) ≤
      K₁.natAbs * K₂.natAbs := by
  have hdvd := integerContent_dvd_product_of_two_Bezout_charts
    F U V K₁ K₂ p q D E₁ E₂ hp hq hpq hF hU hV hcert₁ hcert₂
  have hpos : 0 < K₁.natAbs * K₂.natAbs := by
    exact Nat.mul_pos (Int.natAbs_pos.mpr hK₁) (Int.natAbs_pos.mpr hK₂)
  exact Nat.le_of_dvd hpos hdvd

/-- Uniformity in the source rational: once chartwise certificate
constants have height bounds M₁,M₂, the content of every coprime
specialization is at most their product, without dependence on p or q. -/
theorem integerContent_le_of_two_Bezout_height_bounds
    (F : Polynomial (Polynomial ℤ))
    (U V : ℕ → Polynomial ℤ)
    (K₁ K₂ p q : ℤ) (D E₁ E₂ M₁ M₂ : ℕ)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : Nat.Coprime p.natAbs q.natAbs)
    (hF : ∀ j, (F.coeff j).natDegree ≤ D)
    (hU : ∀ j ∈ F.support, (U j).natDegree ≤ E₁)
    (hV : ∀ j ∈ (reflectedBivariate F D).support,
      (V j).natDegree ≤ E₂)
    (hcert₁ :
      (∑ j ∈ F.support, U j * F.coeff j) = Polynomial.C K₁)
    (hcert₂ :
      (∑ j ∈ (reflectedBivariate F D).support,
        V j * (reflectedBivariate F D).coeff j) = Polynomial.C K₂)
    (hK₁ : K₁ ≠ 0) (hK₂ : K₂ ≠ 0)
    (hbound₁ : K₁.natAbs ≤ M₁) (hbound₂ : K₂.natAbs ≤ M₂) :
    integerContent (clearedBivariate F p q D) ≤ M₁ * M₂ := by
  exact (integerContent_le_product_of_two_Bezout_charts
    F U V K₁ K₂ p q D E₁ E₂ hp hq hpq
      hF hU hV hcert₁ hcert₂ hK₁ hK₂).trans
    (Nat.mul_le_mul hbound₁ hbound₂)

end DiophantineRigidity
