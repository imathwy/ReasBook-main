import Mathlib
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

local notation:max "{}^[" γ:max "]" f:max =>
  f □ (fun x : H ↦ ((((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ)) : EReal))

/-- Helper for Example 12 21: evaluating the Moreau envelope of the indicator of `C` at `x`
reduces its defining infimum to points of `C`. -/
private theorem indicator_moreauEnvelope_apply_eq_iInf_scaled_sq_norm_sub
    (C : Set H) (γ : Set.Ioi (0 : ℝ)) (x : H) :
    ({}^[γ] ι[C]) x =
      ⨅ y : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) := by
  -- Unfold the Moreau envelope and restrict the infimum to the points where the indicator is `0`.
  calc
    ({}^[γ] ι[C]) x
      = ⨅ y : H, (ι[C] y : EReal) +
          ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
            simp [infimalConvolution_apply]
    _ = ⨅ y : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) := by
          apply le_antisymm
          · refine le_iInf ?_
            intro y
            have hle :
                (⨅ z : H, (ι[C] z : EReal) +
                    ((((1 / (2 * (γ : ℝ))) * ‖x - z‖ ^ 2 : ℝ) : EReal))) ≤
                  (ι[C] (y : H) : EReal) +
                    ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) :=
              iInf_le _ (y : H)
            simpa [indicator_apply, y.property] using hle
          · refine le_iInf ?_
            intro y
            by_cases hy : y ∈ C
            · have hle :
                  (⨅ z : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (z : H)‖ ^ 2 : ℝ) : EReal))) ≤
                    ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) :=
                iInf_le
                  (fun z : C ↦
                    ((((1 / (2 * (γ : ℝ))) * ‖x - (z : H)‖ ^ 2 : ℝ) : EReal)))
                  ⟨y, hy⟩
              simpa [indicator_apply, hy] using hle
            · have htop : (ι[C] y : EReal) = ⊤ := by
                simp [indicator_apply, hy]
              rw [htop]
              exact le_top

/-- Helper for Example 12 21: on a nonempty set, the constrained infimum of the scaled translated
square norms equals the same scaling of `Metric.infDist^2`. -/
private theorem scaled_sq_infDist_eq_iInf_scaled_sq_norm_sub
    (C : Set H) (γ : Set.Ioi (0 : ℝ)) (hC : C.Nonempty) (x : H) :
    ((((1 / (2 * (γ : ℝ))) * Metric.infDist x C ^ 2 : ℝ)) : EReal) =
      ⨅ y : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) := by
  let f : ℝ → EReal := fun r ↦ ((((1 / (2 * (γ : ℝ))) * max r 0 ^ 2 : ℝ)) : EReal)
  letI : Nonempty C := hC.to_subtype
  rw [Metric.infDist_eq_iInf]
  have hinf_nonneg : 0 ≤ ⨅ z : C, dist x z := by
    refine le_ciInf ?_
    intro z
    exact dist_nonneg
  have hf_cont : ContinuousAt f (⨅ z : C, dist x z) := by
    -- The positive cutoff-square map is continuous before coercing to `EReal`.
    dsimp [f]
    exact continuous_coe_real_ereal.continuousAt.comp
      (continuousAt_const.mul ((continuousAt_id.max continuousAt_const).pow 2))
  have hf_mono : Monotone f := by
    intro r s hrs
    dsimp [f]
    have hcoef_nonneg : 0 ≤ 1 / (2 * (γ : ℝ)) := by
      exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt γ.2))
    have hmax : max r 0 ≤ max s 0 := max_le_max hrs le_rfl
    have hsq : max r 0 ^ 2 ≤ max s 0 ^ 2 := by
      nlinarith [hmax, le_max_right r 0, le_max_right s 0]
    exact_mod_cast mul_le_mul_of_nonneg_left hsq hcoef_nonneg
  have hmap :
      f (⨅ z : C, dist x z) = ⨅ z : C, f (dist x z) := by
    refine Monotone.map_ciInf_of_continuousAt hf_cont hf_mono ?_
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact dist_nonneg
  -- Apply the cutoff-square map to the canonical `Metric.infDist` infimum formula.
  calc
    ((((1 / (2 * (γ : ℝ))) * (⨅ z : C, dist x z) ^ 2 : ℝ)) : EReal)
      = f (⨅ z : C, dist x z) := by
          simp [f, hinf_nonneg]
    _ = ⨅ z : C, f (dist x z) := hmap
    _ = ⨅ y : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) := by
          simp [f, dist_eq_norm]

/-- Helper for Example 12 21: on a nonempty set, the target `Metric.infEDist` expression agrees
with the scaled real-valued square of `Metric.infDist`. -/
private theorem scaled_sq_infEDist_eq_scaled_sq_infDist
    (C : Set H) (γ : Set.Ioi (0 : ℝ)) (hC : C.Nonempty) (x : H) :
    (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) =
      ((((1 / (2 * (γ : ℝ))) * Metric.infDist x C ^ 2 : ℝ)) : EReal) := by
  have hdist_top_enn : (Metric.infEDist x C : ENNReal) ≠ ⊤ := Metric.infEDist_ne_top hC
  have hdist_top : (Metric.infEDist x C : EReal) ≠ ⊤ := by
    intro htop
    exact hdist_top_enn (by simpa using htop)
  -- Finite `Metric.infEDist` values can be rewritten through `toReal`, which is `Metric.infDist`.
  calc
    (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal)
      = (((Metric.infDist x C ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal) := by
          rw [pow_two,
            ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist x C : EReal) ≠ ⊥),
            ← EReal.coe_toReal hdist_top (by simp : (Metric.infEDist x C : EReal) ≠ ⊥),
            show (2 * (γ : ℝ) : EReal) = ((2 * (γ : ℝ) : ℝ) : EReal) by rfl,
            ← EReal.coe_mul, ← EReal.coe_div]
          simp [Metric.infDist, pow_two]
    _ = ((((1 / (2 * (γ : ℝ))) * Metric.infDist x C ^ 2 : ℝ)) : EReal) := by
          congr 1
          ring

/-- Example 12 21: the `γ`-Moreau envelope of the indicator `ι[C]` is the scaled squared
extended-distance function `x ↦ d(x, C)^2 / (2γ)`, with value `⊤` when `C = ∅`. -/
-- Proof sketch: unfold `{}^[γ] ι[C]`; on points of `C` the indicator contributes `0`, outside
-- `C` it contributes `⊤`, so the infimum reduces to minimizing `‖x - y‖² / (2γ)` over `y ∈ C`.
-- The resulting `EReal`-valued function is the square of the canonical extended distance
-- `Metric.infEDist · C`, scaled by `1 / (2γ)`.
theorem indicator_moreauEnvelope_eq_scaled_sq_infEDist (C : Set H) (γ : Set.Ioi (0 : ℝ)) :
    {}^[γ] ι[C] =
      fun x : H ↦ (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) := by
  funext x
  by_cases hC : C.Nonempty
  · -- On a nonempty set, both sides identify with the same constrained infimum over `C`.
    calc
      ({}^[γ] ι[C]) x
        = ⨅ y : C, ((((1 / (2 * (γ : ℝ))) * ‖x - (y : H)‖ ^ 2 : ℝ) : EReal)) :=
            indicator_moreauEnvelope_apply_eq_iInf_scaled_sq_norm_sub C γ x
      _ = ((((1 / (2 * (γ : ℝ))) * Metric.infDist x C ^ 2 : ℝ)) : EReal) := by
            symm
            exact scaled_sq_infDist_eq_iInf_scaled_sq_norm_sub C γ hC x
      _ = (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) := by
            symm
            exact scaled_sq_infEDist_eq_scaled_sq_infDist C γ hC x
  · -- For the empty set, the Moreau envelope and the extended distance are both identically `⊤`.
    have hleft :
        (⨅ y : H, (ι[C] y : EReal) +
            ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) = ⊤ := by
      have hfun :
          (fun y : H ↦ (ι[C] y : EReal) +
              ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) =
            fun _ : H ↦ (⊤ : EReal) := by
        funext y
        have htop : (ι[C] y : EReal) = ⊤ := by
          simp [Set.not_nonempty_iff_eq_empty.mp hC, indicator_apply]
        rw [htop]
        exact EReal.top_add_coe _
      rw [hfun]
      simp
    have hright :
        (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) = ⊤ := by
      rw [Set.not_nonempty_iff_eq_empty.mp hC, Metric.infEDist_empty, pow_two]
      have hdiv :
          (⊤ : EReal) / (2 * (γ : ℝ) : EReal) = ⊤ := by
        refine EReal.top_div_of_pos_ne_top ?_ ?_
        · change (0 : EReal) < (((2 * (γ : ℝ) : ℝ) : EReal))
          have hreal : 0 < (2 * (γ : ℝ) : ℝ) := by
            exact mul_pos (by norm_num) γ.2
          exact_mod_cast hreal
        · simpa using (EReal.coe_ne_top (2 * (γ : ℝ) : ℝ))
      simpa using hdiv
    calc
      ({}^[γ] ι[C]) x
        = ⨅ y : H, (ι[C] y : EReal) +
            ((((1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
              simp [infimalConvolution_apply]
      _ = ⊤ := hleft
      _ = (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) := by
            symm
            exact hright

end ERealFunction
