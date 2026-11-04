import DiophantineRigidity.CongruenceSpacing
import MahlerLean.FareySeparation

/-!
# Packing of rational arguments in one congruence class

This is the real counting step in Lemma 4.1 after p-adic root balls
have imposed a common integer modulus on cross determinants.

The p-adic covering and the divisor-class summation are not assumed
to be proved here. They remain separate mathematical obligations.
-/

namespace DiophantineRigidity

/-- In one modular class, all distinct reduced rationals with
canonical denominators below 2Q are separated by M/(4Q²).
The modular condition is the concrete cross-determinant divisibility
which will eventually be supplied by the p-adic root-covering lemma. -/
theorem modular_farey_interval_card_le
    (S : Finset ℚ) (l u : ℝ) (Q M : ℕ)
    (hlu : l ≤ u) (hQ : 0 < Q) (hM : 0 < M)
    (hmem : ∀ r ∈ S, l ≤ (r : ℝ) ∧ (r : ℝ) ≤ u)
    (hden : ∀ r ∈ S, r.den < 2 * Q)
    (hcong : ∀ r ∈ S, ∀ s ∈ S, r ≠ s →
      (M : ℤ) ∣ r.num * (s.den : ℤ) - s.num * (r.den : ℤ)) :
    (S.card : ℝ) ≤
      (u - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdelta : (0 : ℝ) < (M : ℝ) / (4 * (Q : ℝ) ^ 2) := by positivity
  apply MahlerLean.card_le_of_separated_values
    S (fun r : ℚ => (r : ℝ)) l u
    ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) hlu hdelta hmem
  intro r hr s hs hrs
  have hrpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hspos : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hrlt : (r.den : ℝ) < 2 * (Q : ℝ) := by exact_mod_cast hden r hr
  have hslt : (s.den : ℝ) < 2 * (Q : ℝ) := by exact_mod_cast hden s hs
  have hprod : (r.den : ℝ) * (s.den : ℝ) < 4 * (Q : ℝ) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hrlt hspos,
      mul_lt_mul_of_pos_left hslt
        (show (0 : ℝ) < 2 * (Q : ℝ) by positivity)]
  have hcross : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 := by
    intro hz
    exact hrs (Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp hz))
  have hsep := cross_modulus_real_separation
    r.num s.num r.den s.den M r.den_pos s.den_pos
    hcross (hcong r hr s hs hrs)
  have hstep :
      (M : ℝ) / (4 * (Q : ℝ) ^ 2) ≤
        (M : ℝ) / ((r.den : ℝ) * (s.den : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Q : ℝ) ^ 2)
      (mul_pos hrpos hspos)).2
    have hnonneg : (0 : ℝ) ≤ M := le_of_lt hMr
    nlinarith [mul_nonneg hnonneg (le_of_lt hprod)]
  exact hstep.trans (by simpa only [Rat.cast_def] using hsep)


/-- A finite collection of congruence classes inherits the packing
bound after summing over classes. Each class uses the same modulus M;
the membership condition is explicit and no p-adic existence theorem
is assumed. -/
theorem modular_farey_finite_classes_card_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ℚ) (t : Finset ι) (classOf : ℚ → ι)
    (l u : ℝ) (Q M : ℕ)
    (hlu : l ≤ u) (hQ : 0 < Q) (hM : 0 < M)
    (hmem : ∀ r ∈ S, l ≤ (r : ℝ) ∧ (r : ℝ) ≤ u)
    (hden : ∀ r ∈ S, r.den < 2 * Q)
    (hclass : ∀ r ∈ S, classOf r ∈ t)
    (hcong : ∀ r ∈ S, ∀ s ∈ S, r ≠ s →
      classOf r = classOf s →
      (M : ℤ) ∣ r.num * (s.den : ℤ) - s.num * (r.den : ℤ)) :
    (S.card : ℝ) ≤ (t.card : ℝ) *
      ((u - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1) := by
  classical
  let parts (i : ι) : Finset ℚ := S.filter (fun r => classOf r = i)
  have hdecomp : S = t.biUnion parts := by
    ext r
    simp only [Finset.mem_biUnion, parts, Finset.mem_filter]
    constructor
    · intro hr
      exact ⟨classOf r, hclass r hr, hr, rfl⟩
    · rintro ⟨i, hi, hr, hri⟩
      exact hr
  have hsum : S.card ≤ ∑ i ∈ t, (parts i).card := by
    rw [hdecomp]
    exact Finset.card_biUnion_le
  have hparts : ∀ i ∈ t,
      ((parts i).card : ℝ) ≤
        (u - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1 := by
    intro i hi
    apply modular_farey_interval_card_le
      (parts i) l u Q M hlu hQ hM
    · intro r hr
      exact hmem r (Finset.mem_filter.mp hr).1
    · intro r hr
      exact hden r (Finset.mem_filter.mp hr).1
    · intro r hr s hs hrs
      obtain ⟨hrS, hrclass⟩ := Finset.mem_filter.mp hr
      obtain ⟨hsS, hsclass⟩ := Finset.mem_filter.mp hs
      exact hcong r hrS s hsS hrs (hrclass.trans hsclass.symm)
  calc
    (S.card : ℝ) ≤ ∑ i ∈ t, ((parts i).card : ℝ) := by
      exact_mod_cast hsum
    _ ≤ ∑ _i ∈ t,
        ((u - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1) := by
      exact Finset.sum_le_sum hparts
    _ = (t.card : ℝ) *
        ((u - l) / ((M : ℝ) / (4 * (Q : ℝ) ^ 2)) + 1) := by
      simp [nsmul_eq_mul]

end DiophantineRigidity
