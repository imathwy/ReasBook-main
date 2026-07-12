import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Manifold
open scoped ContDiff Manifold

-- Semantic Lean search tool unavailable in this environment; the statement below was aligned with
-- the local Section 6.38 chartwise `volume = 0` formulation for manifold measure-zero subsets.

universe uE uH uM

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Definition 6.38-extra-2: a subset `A ⊆ M` has measure zero in a finite-dimensional smooth
manifold with or without boundary when, for every smooth chart `e` on `M`, the corresponding
extended chart image `(e.extend I) '' (A ∩ e.source)` has ambient additive Haar measure zero. -/
def has_measure_zero_in_manifold (A : Set M) : Prop :=
  ∀ (μ : Measure E), μ.IsAddHaarMeasure →
    ∀ e : OpenPartialHomeomorph M H,
    e ∈ IsManifold.maximalAtlas I ∞ M →
      μ ((e.extend I) '' (A ∩ e.source)) = 0

/-- The chartwise vanishing conclusion for the preferred extended chart of a measure-zero subset
of a smooth manifold, for any additive Haar measure on the model space. -/
theorem has_measure_zero_in_manifold.extChartAt_eq_zero (μ : Measure E) (hμ : μ.IsAddHaarMeasure)
    {A : Set M} (hA : has_measure_zero_in_manifold I A) (x : M) :
    μ ((extChartAt I x) '' (A ∩ (extChartAt I x).source)) = 0 := by
  simpa using hA μ hμ (chartAt H x) (IsManifold.chart_mem_maximalAtlas x)

end

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `volume`-specialized chartwise vanishing conclusion for the preferred extended chart of a
measure-zero subset of a smooth manifold. -/
theorem has_measure_zero_in_manifold.extChartAt_volume_eq_zero {A : Set M}
    (hA : has_measure_zero_in_manifold I A) (x : M) :
    volume ((extChartAt I x) '' (A ∩ (extChartAt I x).source)) = 0 :=
  has_measure_zero_in_manifold.extChartAt_eq_zero I volume inferInstance hA x

end
