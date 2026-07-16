import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial

private lemma natDegree_X_sq_sub_X : (((X : Polynomial ℤ) ^ 2) - X).natDegree = 2 := by
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simp

private lemma leadingCoeff_X_sq_sub_X : (((X : Polynomial ℤ) ^ 2) - X).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree (by simp))]
  simp

private noncomputable def xSqSubXModSix : Polynomial (ZMod 6) :=
  Polynomial.map (Int.castRingHom (ZMod 6)) (((X : Polynomial ℤ) ^ 2) - X)

private lemma xSqSubXModSix_isRoot_zero : xSqSubXModSix.IsRoot (0 : ZMod 6) := by
  rw [xSqSubXModSix, Polynomial.IsRoot, Polynomial.eval_map,
    show (0 : ZMod 6) = Int.castRingHom (ZMod 6) 0 by rfl, Polynomial.eval₂_at_apply]
  norm_num

private lemma xSqSubXModSix_isRoot_one : xSqSubXModSix.IsRoot (1 : ZMod 6) := by
  rw [xSqSubXModSix, Polynomial.IsRoot, Polynomial.eval_map,
    show (1 : ZMod 6) = Int.castRingHom (ZMod 6) 1 by rfl, Polynomial.eval₂_at_apply]
  norm_num

private lemma xSqSubXModSix_isRoot_three : xSqSubXModSix.IsRoot (3 : ZMod 6) := by
  rw [xSqSubXModSix, Polynomial.IsRoot, Polynomial.eval_map,
    show (3 : ZMod 6) = Int.castRingHom (ZMod 6) 3 by rfl, Polynomial.eval₂_at_apply]
  norm_num
  decide

private theorem natDegree_lt_natCard_roots_xSqSubX_modSix :
    (((X : Polynomial ℤ) ^ 2) - X).natDegree <
      Nat.card {x : ZMod 6 // xSqSubXModSix.IsRoot x} := by
  let f : Fin 3 → {x : ZMod 6 // xSqSubXModSix.IsRoot x}
    | 0 => ⟨0, xSqSubXModSix_isRoot_zero⟩
    | 1 => ⟨1, xSqSubXModSix_isRoot_one⟩
    | 2 => ⟨3, xSqSubXModSix_isRoot_three⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    · exfalso
      exact (by decide : (0 : ZMod 6) ≠ 1) (by simpa [f] using congrArg Subtype.val hij)
    · exfalso
      exact (by decide : (0 : ZMod 6) ≠ 3) (by simpa [f] using congrArg Subtype.val hij)
    · exfalso
      exact (by decide : (1 : ZMod 6) ≠ 0) (by simpa [f] using congrArg Subtype.val hij)
    · exfalso
      exact (by decide : (1 : ZMod 6) ≠ 3) (by simpa [f] using congrArg Subtype.val hij)
    · exfalso
      exact (by decide : (3 : ZMod 6) ≠ 0) (by simpa [f] using congrArg Subtype.val hij)
    · exfalso
      exact (by decide : (3 : ZMod 6) ≠ 1) (by simpa [f] using congrArg Subtype.val hij)
  have hcard : Nat.card (Fin 3) ≤ Nat.card {x : ZMod 6 // xSqSubXModSix.IsRoot x} :=
    Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at hcard
  rw [natDegree_X_sq_sub_X]
  exact lt_of_lt_of_le (by decide : 2 < 3) hcard

-- Proof sketch: choose an explicit composite modulus such as `6` and the polynomial `X^2 - X`,
-- then exhibit more distinct roots modulo `6` than the degree of the polynomial.
/-- Remark 1.1.80: the degree bound for solutions of a polynomial congruence modulo a prime fails
for composite moduli; equivalently, there exist a composite modulus and an integer polynomial whose
leading coefficient is not divisible by the modulus but which has more solutions modulo that
modulus than its degree. -/
theorem composite_modulus_polynomial_root_bound_fails :
    ∃ (n : ℕ) (_ : 2 ≤ n) (_ : ¬ Nat.Prime n) (P : Polynomial ℤ),
      ¬ ((n : ℤ) ∣ P.leadingCoeff) ∧
        P.natDegree < Nat.card {x : ZMod n // (P.map (Int.castRingHom (ZMod n))).IsRoot x} := by
  refine ⟨6, by decide, by decide, (X : Polynomial ℤ) ^ 2 - X, ?_, ?_⟩
  · rw [leadingCoeff_X_sq_sub_X]
    norm_num
  · simpa [xSqSubXModSix] using natDegree_lt_natCard_roots_xSqSubX_modSix
