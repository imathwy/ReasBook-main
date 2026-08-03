import BauschkeLean.Chap24.Example_24_35
import BauschkeLean.Chap24.Proposition_24_8

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Semantic recall note: the reusable Chapter 24 core owner for the hinge loss is the translated
-- reflection of `positivePartFunction`, so the source-facing scalar hinge-loss API here is built
-- as a thin bridge over Example 24.35 and Proposition 24.8.

section RealLine

/-- The hinge loss `ξ ↦ max 0 (1 - ξ)` as an `]-∞,+∞]`-valued function. -/
def hingeLossFunction : ℝ → Set.Ioi (⊥ : EReal) :=
  fun ξ ↦ positivePartFunction (1 - ξ)

/-- Companion to Example 24.36: the hinge loss is the translated reflection of the scalar
positive-part function from Example 24.35. -/
theorem hingeLossFunction_eq_translateSub_reverse_positivePartFunction :
    hingeLossFunction = fun ξ : ℝ ↦ Function.reverse positivePartFunction (ξ - 1) := by
  funext ξ
  simp [hingeLossFunction]

/-- Evaluating `hingeLossFunction` recovers the source formula `max 0 (1 - ξ)`. -/
@[simp] theorem hingeLossFunction_apply (ξ : ℝ) :
    (hingeLossFunction ξ : EReal) = ((max 0 (1 - ξ) : ℝ) : EReal) := by
  rw [hingeLossFunction]
  change (((1 - ξ)⁺ : ℝ) : EReal) = ((max 0 (1 - ξ) : ℝ) : EReal)
  by_cases hξ : 0 ≤ 1 - ξ
  · rw [posPart_eq_self.2 hξ, max_eq_right hξ]
  · have hξ' : 1 - ξ ≤ 0 := le_of_not_ge hξ
    rw [posPart_eq_zero.2 hξ', max_eq_left hξ']

/-- Example 24.36 (1): the hinge loss is the distance to the closed half-line `[1, +∞[`. -/
theorem hingeLossFunction_eq_distance_Ici_one :
    hingeLossFunction =
      (fun ξ : ℝ ↦ Metric.infDist ξ (Set.Ici (1 : ℝ))).toEReal := by
  funext ξ
  apply Subtype.ext
  rw [hingeLossFunction_apply]
  change ((max 0 (1 - ξ) : ℝ) : EReal) =
      ((Metric.infDist ξ (Set.Ici (1 : ℝ)) : ℝ) : EReal)
  by_cases hξ : ξ ≤ 1
  · have hdist : Metric.infDist ξ (Set.Ici (1 : ℝ)) = 1 - ξ := by
      refine le_antisymm ?_ ?_
      · have hle :
            Metric.infDist ξ (Set.Ici (1 : ℝ)) ≤ dist ξ (1 : ℝ) :=
          Metric.infDist_le_dist_of_mem (show (1 : ℝ) ∈ Set.Ici (1 : ℝ) by simp)
        simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hξ)] using hle
      · rw [Metric.le_infDist ⟨1, by simp⟩]
        intro y hy
        have hy' : 1 ≤ y := hy
        have hξy_nonpos : ξ - y ≤ 0 := sub_nonpos.mpr (le_trans hξ hy')
        have hbound : 1 - ξ ≤ |ξ - y| := by
          simpa [abs_of_nonpos hξy_nonpos] using sub_le_sub_right hy' ξ
        simpa [Real.dist_eq] using hbound
    rw [hdist, max_eq_right (sub_nonneg.mpr hξ)]
  · have hξ' : 1 < ξ := lt_of_not_ge hξ
    have hdist : Metric.infDist ξ (Set.Ici (1 : ℝ)) = 0 := by
      exact Metric.infDist_zero_of_mem (show ξ ∈ Set.Ici (1 : ℝ) by exact le_of_lt hξ')
    rw [hdist, max_eq_left (by linarith)]

/-- The scalar hinge loss belongs to `Γ₀(ℝ)`. -/
theorem hingeLossFunction_mem_gammaZero :
    hingeLossFunction ∈ Γ₀(ℝ) := by
  have hpositivePartReverse : Function.reverse positivePartFunction ∈ Γ₀(ℝ) := by
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ
    simpa [Function.comp, e, Function.reverse] using
      (mem_gammaZero_comp_continuousLinearEquiv positivePartFunction_mem_gammaZero e)
  rw [hingeLossFunction_eq_translateSub_reverse_positivePartFunction]
  simpa using translateSub_mem_gammaZero hpositivePartReverse (1 : ℝ)

/-- Example 24.36 (2): for `γ ∈ ℝ_{++}`, the proximity operator of `γ φ` is the three-branch
formula `(24.68)`. -/
theorem prox_hingeLossFunction_eq_piecewise (γ : PosReal) :
    Prox[γ, hingeLossFunction, hingeLossFunction_mem_gammaZero] =
      fun ξ : ℝ ↦
        if ξ < 1 - (γ : ℝ) then ξ + (γ : ℝ)
        else if 1 - (γ : ℝ) ≤ ξ ∧ ξ ≤ 1 then 1
        else ξ := by
  sorry

end RealLine

end

end ERealFunction
