import BauschkeLean.Chap24.Corollary_24_15
import BauschkeLean.Chap24.Example_24_36

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section BasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall/local precedent: `lean_leansearch` only surfaced unrelated generic max/proximity
-- results, so this item uses the local scalar hinge-loss owner from Example 24.36 together with
-- the rank-one pullback prox formula from Corollary 24.15.

/-- The Example 24.37 hinge loss pulled back along the inner-product map `x ↦ ⟪x, u⟫_ℝ`. -/
def hingeLossFunctionAlong (u : H) : H → Set.Ioi (⊥ : EReal) :=
  hingeLossFunction ∘ innerSL ℝ u

omit [CompleteSpace H] in
/-- Evaluating `hingeLossFunctionAlong u` recovers the source formula
`x ↦ max 0 (1 - ⟪x, u⟫_ℝ)`. -/
@[simp] theorem hingeLossFunctionAlong_apply (u x : H) :
    (hingeLossFunctionAlong u x : EReal) = ((max 0 (1 - ⟪x, u⟫_ℝ) : ℝ) : EReal) := by
  simp [hingeLossFunctionAlong, real_inner_comm]

/-- The inner-product pullback of the scalar hinge loss belongs to `Γ₀(H)` when `u ≠ 0`. -/
theorem hingeLossFunctionAlong_mem_gammaZero_of_ne_zero
    (u : H) (hu : u ≠ 0) :
    hingeLossFunctionAlong u ∈ Γ₀(H) := by
  simpa [hingeLossFunctionAlong] using
    comp_innerSL_mem_gammaZero_of_ne_zero hingeLossFunction hingeLossFunction_mem_gammaZero u hu

/-- Example 24.37: if `u ≠ 0` and
`f x = max 0 (1 - ⟪x, u⟫_ℝ)`, then `Prox_f` is the three-branch formula `(24.70)`. -/
theorem prox_hingeLossFunctionAlong_eq_piecewise_of_ne_zero
    (u : H) (hu : u ≠ 0) :
    Prox[hingeLossFunctionAlong u, hingeLossFunctionAlong_mem_gammaZero_of_ne_zero u hu] =
      fun x : H ↦
        if ⟪x, u⟫_ℝ < 1 - ‖u‖ ^ 2 then
          x + u
        else if 1 - ‖u‖ ^ 2 ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ 1 then
          x + ((1 - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u
        else
          x := by
  funext x
  have hprox :
      Prox[hingeLossFunctionAlong u, hingeLossFunctionAlong_mem_gammaZero_of_ne_zero u hu] x =
        x + ((Prox[normSqPosReal u hu, hingeLossFunction, hingeLossFunction_mem_gammaZero]
          ⟪x, u⟫_ℝ - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
    simpa [hingeLossFunctionAlong] using
      prox_comp_innerSL_eq_add_div_normSq_smul_of_ne_zero
        hingeLossFunction hingeLossFunction_mem_gammaZero u hu x
  have hscalar :
      Prox[normSqPosReal u hu, hingeLossFunction, hingeLossFunction_mem_gammaZero] ⟪x, u⟫_ℝ =
        if ⟪x, u⟫_ℝ < 1 - ‖u‖ ^ 2 then
          ⟪x, u⟫_ℝ + ‖u‖ ^ 2
        else if 1 - ‖u‖ ^ 2 ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ 1 then
          1
        else
          ⟪x, u⟫_ℝ := by
    simpa [normSqPosReal_coe] using
      congrFun (prox_hingeLossFunction_eq_piecewise (normSqPosReal u hu)) ⟪x, u⟫_ℝ
  have hu_norm_sq_ne : ‖u‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  rw [hprox, hscalar]
  by_cases hlt : ⟪x, u⟫_ℝ < 1 - ‖u‖ ^ 2
  · rw [if_pos hlt, if_pos hlt]
    simp [div_self hu_norm_sq_ne]
  · by_cases hmid : 1 - ‖u‖ ^ 2 ≤ ⟪x, u⟫_ℝ ∧ ⟪x, u⟫_ℝ ≤ 1
    · rw [if_neg hlt, if_pos hmid, if_neg hlt, if_pos hmid]
    · rw [if_neg hlt, if_neg hmid, if_neg hlt, if_neg hmid]
      simp

end BasicProperties

end

end ERealFunction
