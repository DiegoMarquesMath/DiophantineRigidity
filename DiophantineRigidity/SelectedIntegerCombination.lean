import DiophantineRigidity.SelectedCombination

/-!
# Integral selected combinations and their coefficient heights

The actual auxiliary polynomial of Lemma 4.1 has coefficients in ℤ:
  W_t(X) = ∑_{0≤j≤k} t^j V_j(X).
We connect this exact integral polynomial to the previously checked
complex root-avoidance construction, then prove the uniform coefficient
bound.

The bound is deliberately explicit:
  H(W_t) ≤ (k+1)(t+1)^k H(F)
and hence H(W_t) ≤ (k+1)(kD+1)^k H(F) when 0≤t≤kD.
The constants depend only on k,D, not on the coefficient height.
-/

noncomputable section
namespace DiophantineRigidity

/-- The same selected polynomial, now in ℤ[X], not merely ℂ[X]. -/
def selectedIntegerCombination (V : ℕ → Polynomial ℤ)
    (k t : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (k + 1), Polynomial.C ((t : ℤ) ^ j) * V j

/-- The coefficient formula before estimating its absolute value. -/
theorem selectedIntegerCombination_coeff
    (V : ℕ → Polynomial ℤ) (k t n : ℕ) :
    (selectedIntegerCombination V k t).coeff n =
      ∑ j ∈ Finset.range (k + 1), (t : ℤ) ^ j * (V j).coeff n := by
  classical
  unfold selectedIntegerCombination
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.coeff_C_mul]

/-- Evaluating the integer combination in ℂ gives the expected
finite sum of evaluations of the integer coefficient polynomials. -/
theorem selectedIntegerCombination_eval_complex
    (V : ℕ → Polynomial ℤ) (k t : ℕ) (ρ : ℂ) :
    (selectedIntegerCombination V k t).eval₂ (Int.castRingHom ℂ) ρ =
      ∑ j ∈ Finset.range (k + 1),
        (V j).eval₂ (Int.castRingHom ℂ) ρ * (t : ℂ) ^ j := by
  classical
  unfold selectedIntegerCombination
  rw [Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  have hcast :
      (Int.castRingHom ℂ) ((t : ℤ) ^ j) = (t : ℂ) ^ j := by
    simp
  rw [hcast]
  exact mul_comm _ _

/-- Explicit bridge to the complex polynomial already selected by
the root-avoidance lemma. -/
theorem selectedIntegerCombination_as_complex
    (V : ℕ → Polynomial ℤ) (k t : ℕ) (ρ : ℂ) :
    (selectedIntegerCombination V k t).eval₂ (Int.castRingHom ℂ) ρ =
      (selectedCombination
        (fun j => (V j).map (Int.castRingHom ℂ)) k t).eval ρ := by
  rw [selectedIntegerCombination_eval_complex, selectedCombination_eval]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_map]

/-- Choose an actual integer polynomial W_t using the same t across
all complex points in a finite set. -/
theorem exists_selectedIntegerCombination_nonzero_on
    (S : Finset ℂ) (V : ℕ → Polynomial ℤ)
    (k D : ℕ) (hcard : S.card ≤ D)
    (hnoCommon : ∀ ρ ∈ S, ∃ j ≤ k,
      (V j).eval₂ (Int.castRingHom ℂ) ρ ≠ 0) :
    ∃ t : ℕ, t ≤ k * D ∧
      ∀ ρ ∈ S,
        (selectedIntegerCombination V k t).eval₂
          (Int.castRingHom ℂ) ρ ≠ 0 := by
  let VC : ℕ → Polynomial ℂ :=
    fun j => (V j).map (Int.castRingHom ℂ)
  have hVC : ∀ ρ ∈ S, ∃ j ≤ k, (VC j).eval ρ ≠ 0 := by
    intro ρ hρ
    obtain ⟨j, hj, hnonzero⟩ := hnoCommon ρ hρ
    refine ⟨j, hj, ?_⟩
    simpa [VC, Polynomial.eval_map] using hnonzero
  obtain ⟨t, ht, havoid⟩ :=
    exists_selectedCombination_nonzero_on S VC k D hcard hVC
  refine ⟨t, ht, ?_⟩
  intro ρ hρ
  rw [selectedIntegerCombination_as_complex]
  simpa only [VC] using havoid ρ hρ

/-- The coefficient height is bounded linearly by the original
height and polynomially (with a fixed exponent) in t. -/
theorem selectedIntegerCombination_coeff_abs_le
    (V : ℕ → Polynomial ℤ) (k t n : ℕ) (H : ℤ)
    (hV : ∀ j ≤ k, ∀ i, |(V j).coeff i| ≤ H) :
    |(selectedIntegerCombination V k t).coeff n| ≤
      ((k + 1 : ℕ) : ℤ) * ((t : ℤ) + 1) ^ k * H := by
  classical
  rw [selectedIntegerCombination_coeff]
  have ht : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have ht1 : (0 : ℤ) ≤ (t : ℤ) + 1 := by omega
  have hterm :
      ∀ j ∈ Finset.range (k + 1),
        |(t : ℤ) ^ j * (V j).coeff n| ≤ ((t : ℤ) + 1) ^ k * H := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (t : ℤ) ^ j ≤ ((t : ℤ) + 1) ^ k := by
      calc
        (t : ℤ) ^ j ≤ ((t : ℤ) + 1) ^ j := by
          gcongr
          omega
        _ ≤ ((t : ℤ) + 1) ^ k := by
          gcongr
          omega
    calc
      |(t : ℤ) ^ j * (V j).coeff n| =
          (t : ℤ) ^ j * |(V j).coeff n| := by
            rw [abs_mul, abs_pow, abs_of_nonneg ht]
      _ ≤ ((t : ℤ) + 1) ^ k * |(V j).coeff n| :=
          mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
      _ ≤ ((t : ℤ) + 1) ^ k * H :=
          mul_le_mul_of_nonneg_left (hV j hjk n) (pow_nonneg ht1 k)
  calc
    |∑ j ∈ Finset.range (k + 1), (t : ℤ) ^ j * (V j).coeff n| ≤
        ∑ j ∈ Finset.range (k + 1),
          |(t : ℤ) ^ j * (V j).coeff n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (k + 1), ((t : ℤ) + 1) ^ k * H :=
      Finset.sum_le_sum (fun j hj => hterm j hj)
    _ = ((k + 1 : ℕ) : ℤ) * ((t : ℤ) + 1) ^ k * H := by
      simp
      ring

/-- A fully uniform coefficient-height bound, using t≤kD. -/
theorem selectedIntegerCombination_coeff_abs_le_kD
    (V : ℕ → Polynomial ℤ) (k D t n : ℕ) (H : ℤ)
    (ht : t ≤ k * D) (hH : 0 ≤ H)
    (hV : ∀ j ≤ k, ∀ i, |(V j).coeff i| ≤ H) :
    |(selectedIntegerCombination V k t).coeff n| ≤
      ((k + 1 : ℕ) : ℤ) * (((k * D : ℕ) : ℤ) + 1) ^ k * H := by
  have hb := selectedIntegerCombination_coeff_abs_le V k t n H hV
  calc
    |(selectedIntegerCombination V k t).coeff n| ≤
        ((k + 1 : ℕ) : ℤ) * ((t : ℤ) + 1) ^ k * H := hb
    _ ≤ ((k + 1 : ℕ) : ℤ) * (((k * D : ℕ) : ℤ) + 1) ^ k * H := by
      have htk : (t : ℤ) + 1 ≤ (((k * D : ℕ) : ℤ) + 1) := by
        exact_mod_cast Nat.add_le_add_right ht 1
      have hpow : ((t : ℤ) + 1) ^ k ≤ (((k * D : ℕ) : ℤ) + 1) ^ k := by
        gcongr
      have hcoeff : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hcoeff) hH

end DiophantineRigidity
