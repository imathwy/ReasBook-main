import chapter1_reference_format.Chap01.Definition_1_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NNReal

-- Proof sketch: the forward direction is the standard lemma that a nonarchimedean absolute value
-- sends every integer to something at most `1`; for the converse, expand `(x + y)^k` by the
-- binomial theorem, use the hypothesis on integer binomial coefficients, and let `k → ∞`.

namespace Rat.AbsoluteValue

/-- The real-valued form of Proposition 1.2.18, which is the canonical core statement behind the
chapter's `ℝ≥0`-valued bridge via `AbsoluteValue.toReal`. -/
theorem isNonarchimedean_iff_intCast_le_one
    (v : AbsoluteValue ℚ ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℤ, v (n : ℚ) ≤ 1 := by
  constructor
  · intro hv n
    exact IsNonarchimedean.apply_intCast_le_one_of_isNonarchimedean hv
  · intro h
    by_cases hv_nontriv : v.IsNontrivial
    · have hnat : ∀ n : ℕ, v (n : ℚ) ≤ 1 := fun n ↦ by
        simpa using h (n : ℤ)
      obtain ⟨p, ⟨hp, hp_equiv⟩, _⟩ := equiv_padic_of_bounded hv_nontriv hnat
      obtain ⟨c, hc, hc_eq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hp_equiv.symm
      intro x y
      calc
        v (x + y) = padic p (x + y) ^ c := by
          simpa using (congrFun hc_eq (x + y)).symm
        _ ≤ max (padic p x) (padic p y) ^ c := by
          gcongr
          simpa [padic_eq_padicNorm] using
            padicNorm.nonarchimedean
        _ = max (padic p x ^ c) (padic p y ^ c) := by
          rw [Real.rpow_max]
          all_goals positivity
        _ = max (v x) (v y) := by
          rw [congrFun hc_eq x, congrFun hc_eq y]
    · intro x y
      by_cases hxy : x + y = 0
      · simp [hxy, v.nonneg]
      · rcases eq_or_ne x 0 with hx | hx
        · have hy : y ≠ 0 := by
            intro hy
            exact hxy (by simp [hx, hy])
          calc
            v (x + y) = 1 := AbsoluteValue.not_isNontrivial_apply hv_nontriv hxy
            _ ≤ max (v x) (v y) := by
              rw [hx, map_zero, AbsoluteValue.not_isNontrivial_apply hv_nontriv hy]
              simp
        · calc
            v (x + y) = 1 := AbsoluteValue.not_isNontrivial_apply hv_nontriv hxy
            _ ≤ max (v x) (v y) := by
              rw [AbsoluteValue.not_isNontrivial_apply hv_nontriv hx]
              exact le_max_left _ _

end Rat.AbsoluteValue

/-- Proposition 1.2.18: an absolute value on `ℚ` is nonarchimedean exactly when every integer has
absolute value at most `1`. -/
theorem rat_absoluteValue_isNonarchimedean_iff_intCast_le_one (v : AbsoluteValue ℚ ℝ≥0) :
    IsNonarchimedean v ↔ ∀ n : ℤ, v (n : ℚ) ≤ 1 := by
  constructor
  · intro hv n
    have hv_real : IsNonarchimedean v.toReal := fun x y ↦ by
      exact_mod_cast hv x y
    exact_mod_cast
      (Rat.AbsoluteValue.isNonarchimedean_iff_intCast_le_one v.toReal).1 hv_real n
  · intro h
    have hv_real : IsNonarchimedean v.toReal :=
      (Rat.AbsoluteValue.isNonarchimedean_iff_intCast_le_one v.toReal).2 fun n ↦ by
        exact_mod_cast h n
    intro x y
    exact_mod_cast hv_real x y
