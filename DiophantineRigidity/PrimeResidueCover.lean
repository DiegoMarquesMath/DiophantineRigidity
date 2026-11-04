import Mathlib

/-!
# Root classes modulo a prime: first p-adic covering checkpoint

Let P be an integer polynomial of degree at most D. When its reduction
to ZMod ℓ is nonzero (i.e. some coefficient is an ℓ-adic unit), at most
D residue classes modulo ℓ can have P(x) = 0.

This is the b ≤ D / ceil(b/D)=1 base case of the required p-adic
covering estimate. Prime powers ℓ^b with b>D still require a genuine
Lagrange-interpolation valuation argument and are not proved here.
-/

namespace DiophantineRigidity

/-- The number of residue classes modulo a prime at which a nonzero
reduced integer polynomial vanishes is bounded by its original degree.

No squarefreeness, simple-root, or nonvanishing-discriminant hypothesis
is imposed: repeated roots are covered as well. -/
theorem prime_residue_root_classes_card_le
    (ℓ D : ℕ) [Fact (Nat.Prime ℓ)]
    (P : Polynomial ℤ)
    (hP : P.map (Int.castRingHom (ZMod ℓ)) ≠ 0)
    (hD : P.natDegree ≤ D) :
    ((Finset.univ : Finset (ZMod ℓ)).filter
      (fun x => (P.map (Int.castRingHom (ZMod ℓ))).eval x = 0)).card ≤ D := by
  classical
  let R : Polynomial (ZMod ℓ) := P.map (Int.castRingHom (ZMod ℓ))
  let S : Finset (ZMod ℓ) := Finset.univ.filter (fun x => R.eval x = 0)
  change S.card ≤ D
  by_contra hn
  have hlarge : D < S.card := Nat.lt_of_not_ge hn
  have hdegree : R.natDegree ≤ D :=
    (Polynomial.natDegree_map_le).trans hD
  have heval : ∀ x ∈ S, R.eval x = 0 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    R S heval (lt_of_le_of_lt hdegree hlarge)
  exact hP hzero

end DiophantineRigidity
