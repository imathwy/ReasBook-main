import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

section

open scoped Rockafellar
open Function (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem)

universe u

variable {X : Type u} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIciTopology 𝕜] [Zero 𝕜]

/-- Canonical owner form behind Text 7.0.14: for any set in any topological space, the closure of
its indicator is the indicator of the set closure. -/
theorem lowerSemicontinuousHull_indicator_eq_indicator_closure (C : Set X) :
    cl((δ[𝕜](· | C))) = (δ[𝕜](· | closure C)) := by
  have hepi :
      closure (epi (δ[𝕜](· | C))) = epi (δ[𝕜](· | closure C)) := by
    calc
      closure (epi (δ[𝕜](· | C)))
          = closure (C ×ˢ Set.Ici (0 : 𝕜)) := by rw [epi_indicator_eq_prod]
      _ = closure C ×ˢ Set.Ici (0 : 𝕜) := by simp [closure_prod_eq]
      _ = epi (δ[𝕜](· | closure C)) := by rw [epi_indicator_eq_prod]
  ext x
  rw [lowerSemicontinuousHull, hepi]
  by_cases hx : x ∈ closure C
  · have hle :
        verticalInfimum (epi (δ[𝕜](· | closure C))) x ≤ (0 : WithBotTop 𝕜) :=
      verticalInfimum_le_of_mem <| by simp [indicator_def, hx]
    have hge :
        (0 : WithBotTop 𝕜) ≤
          verticalInfimum (epi (δ[𝕜](· | closure C))) x := by
      rw [verticalInfimum_eq_sInf]
      refine le_sInf ?_
      rintro _ ⟨μ, hμ, rfl⟩
      simpa [indicator_def, hx] using hμ
    have hvi :
        verticalInfimum (epi (δ[𝕜](· | closure C))) x = (0 : WithBotTop 𝕜) := by
      exact le_antisymm hle hge
    rw [hvi]
    simp [hx]
  · rw [Function.verticalInfimum_eq_sInf]
    simp [indicator_def, hx]

-- Proof sketch: specialize the canonical indicator-closure theorem to the set `Metric.ball x r`.
/-- Metric-ball specialization of the indicator-closure owner theorem. -/
theorem lowerSemicontinuousHull_indicator_ball_eq_indicator_closure_ball
    {E : Type*} [PseudoMetricSpace E] (x : E) (r : ℝ) :
    cl((δ[𝕜](· | Metric.ball x r))) =
      (δ[𝕜](· | closure (Metric.ball x r))) := by
  simpa using
    (lowerSemicontinuousHull_indicator_eq_indicator_closure
      (X := E) (C := Metric.ball x r))

-- Proof sketch: this is the `x = 0`, `r = 1` specialization of the ball-level bridge.
/-- Text 7.0.14 at intrinsic metric ambient level: for the open unit ball around `0`, the closure
of its indicator is the indicator of its closure. The source's `R²` open-unit-disk statement is
the Euclidean two-dimensional specialization of this theorem. -/
theorem lowerSemicontinuousHull_indicatorFunction_unitDisk_eq_indicatorFunction_closure_unitDisk
    {E : Type*} [PseudoMetricSpace E] [Zero E] :
    cl((δ[𝕜](· | Metric.ball (0 : E) (1 : ℝ)))) =
      (δ[𝕜](· | closure (Metric.ball (0 : E) (1 : ℝ)))) := by
  simpa using
    (lowerSemicontinuousHull_indicator_ball_eq_indicator_closure_ball
      (𝕜 := 𝕜) (x := (0 : E)) (r := (1 : ℝ)))

end
