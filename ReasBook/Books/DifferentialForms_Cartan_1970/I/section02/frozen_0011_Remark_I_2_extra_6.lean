import Mathlib
import cartan.I.section02.«frozen_0010_Proposition_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped NNReal ENNReal PowerSeries
open PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- Remark I.2-extra-6: if `r` satisfies the majorant inequality from Proposition `5.1` and
`T(0) = 0`, then on the closed disk `‖z‖ ≤ r` the function defined by the composed formal series
`U = S ∘ T` agrees with the composite of the functions defined by `S` and `T`. -/
theorem scalar_series_comp_eqOn_closedBall_of_majorant
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0) {r : ℝ≥0}
    (h : (∑' n : ℕ, (‖coeff n T‖₊ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) <
      S.radius) :
    Set.EqOn (fun z ↦ PowerSeries.sum (S.subst T) z)
      (fun z ↦ S.sum (T.sum z))
      (Metric.closedBall (0 : 𝕜) (r : ℝ)) := by
  intro z hz
  have hz' : ‖z‖₊ ≤ r := by
    simpa using mem_closedBall_zero_iff.mp hz
  simpa using (scalar_series_sum_comp_eq_comp_sum_of_le S T hT0 h hz').symm

/-- If `S` and `T` have nonzero radii of convergence and `T(0) = 0`, then after shrinking to a
sufficiently small closed disk around `0`, the sum of the composed formal series agrees with the
composite of the summed functions. -/
theorem scalar_series_comp_eqOn_small_closedBall
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0)
    (hT : T.radius ≠ 0) :
    ∃ r : ℝ≥0, 0 < r ∧
      Set.EqOn (fun z ↦ PowerSeries.sum (S.subst T) z)
        (fun z ↦ S.sum (T.sum z))
        (Metric.closedBall (0 : 𝕜) (r : ℝ)) := by
  rcases exists_pos_scalar_series_comp_majorant S T hS hT with ⟨r, hr, hmajorant⟩
  exact ⟨r, hr, scalar_series_comp_eqOn_closedBall_of_majorant S T hT0 hmajorant⟩
