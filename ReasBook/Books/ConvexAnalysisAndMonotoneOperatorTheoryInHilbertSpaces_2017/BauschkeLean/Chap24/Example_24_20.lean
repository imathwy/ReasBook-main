import Mathlib
import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap14.Example_14_5

-- Domain sampling:
-- - `core/canonical`: Chapter 14 owns the scaled-norm proximal operator through
--   `proximityOperator_scaledNorm_eq_softThresholder` and `proximityOperator_scaledNorm_apply`.
-- - `source-facing`: this file keeps the textbook formulas from Example 24.20 as thin bridge
--   views of that owner.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 24.20: for `γ ∈ ℝ_{++}` and `x ∈ H`, the proximity operator of
`γ ‖·‖` satisfies formula `(24.18)`,
`Prox_{γ ‖·‖} x = (1 - γ / max {‖x‖, γ}) x`. -/
theorem example_24_20_1_proximityOperator_scaledNorm_eq_one_sub_div_max_smul
    (γ : Set.Ioi (0 : ℝ)) (x : H) :
    Prox[scaledNormKernelOfPos γ, scaledNormKernelOfPos_mem_gammaZero γ] x =
      (1 - (γ : ℝ) / max ‖x‖ (γ : ℝ)) • x := by
  by_cases hx : (γ : ℝ) < ‖x‖
  · rw [proximityOperator_scaledNorm_apply γ x, if_pos hx]
    simp [max_eq_left hx.le]
  · rw [proximityOperator_scaledNorm_apply γ x, if_neg hx]
    have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    simp [max_eq_right (le_of_not_gt hx), hγ_ne]

end Hilbert

section Real

/-- Helper for Example 24.20: on `ℝ`, the radial shrinkage factor from `(24.18)` equals the
soft-threshold scalar formula `sign(x) * max (|x| - γ) 0`. -/
lemma radialShrinkMul_eq_sign_mul_max
    (γ : Set.Ioi (0 : ℝ)) (x : ℝ) :
    (1 - (γ : ℝ) / max |x| (γ : ℝ)) * x =
      Real.sign x * max (|x| - (γ : ℝ)) 0 := by
  -- Split into the active shrinkage branch and the vanishing branch.
  by_cases hγx : (γ : ℝ) < |x|
  · by_cases hx_nonneg : 0 ≤ x
    · have hx_pos : 0 < x := by
        have hγ_lt_x : (γ : ℝ) < x := by
          simpa [abs_of_nonneg hx_nonneg] using hγx
        exact lt_trans γ.2 hγ_lt_x
      have hγ_lt_x : (γ : ℝ) < x := by
        simpa [abs_of_nonneg hx_nonneg] using hγx
      -- On the positive branch, both sides reduce to `x - γ`.
      rw [max_eq_left hγx.le, Real.sign_of_pos hx_pos, abs_of_nonneg hx_nonneg,
        max_eq_left (sub_nonneg.mpr hγ_lt_x.le)]
      field_simp [ne_of_gt hx_pos]
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hx_ne : x ≠ 0 := ne_of_lt hx_neg
      have hγ_lt_negx : (γ : ℝ) < -x := by
        simpa [abs_of_neg hx_neg] using hγx
      -- On the negative branch, both sides reduce to `x + γ`.
      rw [max_eq_left hγx.le, Real.sign_of_neg hx_neg, abs_of_neg hx_neg,
        max_eq_left (sub_nonneg.mpr hγ_lt_negx.le)]
      field_simp [hx_ne]
      ring
  · have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    have hsub_nonpos : |x| - (γ : ℝ) ≤ 0 := sub_nonpos.mpr (le_of_not_gt hγx)
    -- Inside the threshold ball, both formulas vanish.
    rw [max_eq_right (le_of_not_gt hγx), max_eq_right hsub_nonpos, div_self hγ_ne]
    simp

/-- Helper for Example 24.20: the scalar soft-threshold formula equals the three-branch
expression from `(24.19)`. -/
lemma signMulMax_eq_softThresholdPiecewise
    (γ : Set.Ioi (0 : ℝ)) (x : ℝ) :
    Real.sign x * max (|x| - (γ : ℝ)) 0 =
      if x < -(γ : ℝ) then x + (γ : ℝ)
      else if x ≤ (γ : ℝ) then 0
      else x - (γ : ℝ) := by
  -- Split by the two threshold inequalities appearing in the textbook formula.
  by_cases hx_left : x < -(γ : ℝ)
  · have hnegγ_neg : -(γ : ℝ) < 0 := neg_lt_zero.mpr γ.2
    have hx_neg : x < 0 := lt_trans hx_left hnegγ_neg
    have hγ_lt_negx : (γ : ℝ) < -x := by linarith
    -- Beyond the left threshold, the soft-threshold output is `x + γ`.
    rw [if_pos hx_left, Real.sign_of_neg hx_neg, abs_of_neg hx_neg,
      max_eq_left (sub_nonneg.mpr hγ_lt_negx.le)]
    ring
  · rw [if_neg hx_left]
    by_cases hx_mid : x ≤ (γ : ℝ)
    · have hnegγ_le_x : -(γ : ℝ) ≤ x := le_of_not_gt hx_left
      have habs_le : |x| ≤ (γ : ℝ) := abs_le.mpr ⟨by linarith, hx_mid⟩
      -- In the middle branch, `|x| ≤ γ`, so the output is `0`.
      rw [if_pos hx_mid, max_eq_right (sub_nonpos.mpr habs_le)]
      simp
    · have hγ_lt_x : (γ : ℝ) < x := lt_of_not_ge hx_mid
      have hx_pos : 0 < x := lt_trans γ.2 hγ_lt_x
      -- Beyond the right threshold, the soft-threshold output is `x - γ`.
      rw [if_neg hx_mid, Real.sign_of_pos hx_pos, abs_of_pos hx_pos,
        max_eq_left (sub_nonneg.mpr hγ_lt_x.le)]
      ring

/-- Helper for Example 24.20: on `ℝ`, formula `(24.18)` reduces to the soft-threshold map
`x ↦ sign(x) max {|x| - γ, 0}`. -/
theorem example_24_20_2_proximityOperator_scaledNorm_real_eq_sign_mul_max
    (γ : Set.Ioi (0 : ℝ)) :
    Prox[scaledNormKernelOfPos γ, scaledNormKernelOfPos_mem_gammaZero γ] =
      fun x : ℝ ↦ Real.sign x * max (|x| - (γ : ℝ)) 0 := by
  ext x
  -- Reuse the Hilbert-space formula `(24.18)` specialized to `ℝ`.
  rw [example_24_20_1_proximityOperator_scaledNorm_eq_one_sub_div_max_smul (H := ℝ) γ x]
  -- The remaining step is the scalar bridge from radial shrinkage to soft thresholding.
  simpa [Real.norm_eq_abs, smul_eq_mul] using radialShrinkMul_eq_sign_mul_max γ x

/-- Example 24.20 (3): on `ℝ`, the soft-threshold formula is the three-branch expression
from `(24.19)`. -/
theorem example_24_20_3_proximityOperator_scaledNorm_real_eq_piecewise
    (γ : Set.Ioi (0 : ℝ)) :
    Prox[scaledNormKernelOfPos γ, scaledNormKernelOfPos_mem_gammaZero γ] =
      fun x : ℝ ↦
        if x < -(γ : ℝ) then x + (γ : ℝ)
        else if x ≤ (γ : ℝ) then 0
        else x - (γ : ℝ) := by
  ext x
  -- Rewrite through the soft-threshold formula from theorem (2).
  rw [example_24_20_2_proximityOperator_scaledNorm_real_eq_sign_mul_max γ]
  -- The scalar normalization is packaged in the companion piecewise lemma.
  exact signMulMax_eq_softThresholdPiecewise γ x

end Real

end

end ERealFunction
