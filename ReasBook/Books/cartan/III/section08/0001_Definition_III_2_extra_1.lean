import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Metric Real Set

universe u

/-- Definition III.2-extra-1: a continuous function on `D` has the mean value property if, for
every closed disc contained in `D`, its value at the center equals the average of its values on the
boundary circle. -/
class HasMeanValuePropertyOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (D : Set ℂ) : Prop where
  continuousOn : ContinuousOn f D
  circleAverage_eq {c : ℂ} {R : ℝ} (hclosed : closedBall c |R| ⊆ D) :
    circleAverage f c R = f c

namespace HasMeanValuePropertyOn

variable
  {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℂ → E} {D : Set ℂ}

/-- Composing with a real continuous linear map preserves the mean value property. -/
theorem comp_CLM [CompleteSpace E] [CompleteSpace F]
    (hf : HasMeanValuePropertyOn f D) (L : E →L[ℝ] F) :
    HasMeanValuePropertyOn (L ∘ f) D where
  continuousOn := L.continuous.comp_continuousOn hf.continuousOn
  circleAverage_eq hclosed := by
    calc
      circleAverage (L ∘ f) _ _ = L (circleAverage f _ _) := by
        rw [L.circleAverage_comp_comm
          ((hf.continuousOn.mono (sphere_subset_closedBall.trans hclosed)).circleIntegrable')]
      _ = L (f _) := by rw [hf.circleAverage_eq hclosed]
      _ = (L ∘ f) _ := rfl

end HasMeanValuePropertyOn

/-- A complex-differentiable function has the mean value property on its domain. -/
theorem DifferentiableOn.hasMeanValuePropertyOn {f : ℂ → ℂ} {D : Set ℂ}
    (hf : DifferentiableOn ℂ f D) : HasMeanValuePropertyOn f D where
  continuousOn := hf.continuousOn
  circleAverage_eq hclosed := (hf.diffContOnCl_ball hclosed).circleAverage

/-- The real part of a complex-valued function with the mean value property again has the mean
value property. -/
theorem HasMeanValuePropertyOn.real_part {f : ℂ → ℂ} {D : Set ℂ}
    (hf : HasMeanValuePropertyOn f D) :
    HasMeanValuePropertyOn (fun z ↦ (f z).re) D := by
  simpa [Function.comp_apply] using hf.comp_CLM reCLM

/-- The imaginary part of a complex-valued function with the mean value property again has the mean
value property. -/
theorem HasMeanValuePropertyOn.imaginary_part {f : ℂ → ℂ} {D : Set ℂ}
    (hf : HasMeanValuePropertyOn f D) :
    HasMeanValuePropertyOn (fun z ↦ (f z).im) D := by
  simpa [Function.comp_apply] using hf.comp_CLM imCLM
