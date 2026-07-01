import Mathlib

open Metric Set

variable {F : Type*} [NormedAddCommGroup F]

/-- The supremum of `‖f z‖` on the centered circle of radius `r`. -/
noncomputable def circleSupNorm (f : ℂ → F) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' sphere (0 : ℂ) r)

/-- If `‖f‖` is bounded above on the centered circle of radius `r`, then each boundary value is
bounded by `circleSupNorm f r`. -/
theorem norm_le_circleSupNorm_of_bddAbove {f : ℂ → F} {r : ℝ} {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) r)
    (hB : BddAbove ((fun w : ℂ ↦ ‖f w‖) '' sphere (0 : ℂ) r)) :
    ‖f z‖ ≤ circleSupNorm f r := by
  exact le_csSup hB (mem_image_of_mem (fun w : ℂ ↦ ‖f w‖) hz)

/-- A function continuous on the centered circle of radius `r` is pointwise bounded there by
`circleSupNorm f r`. -/
theorem ContinuousOn.norm_le_circleSupNorm {f : ℂ → F} {r : ℝ}
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    ‖f z‖ ≤ circleSupNorm f r := by
  exact norm_le_circleSupNorm_of_bddAbove hz
    ((isCompact_sphere (0 : ℂ) r).bddAbove_image hf.norm)
