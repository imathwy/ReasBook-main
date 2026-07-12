import SmoothManifolds_Lee_2012.Chap06.Sec06_39.Corollary_6_11
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open MeasureTheory
open scoped ContDiff Manifold

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold`, Corollary 6.11's canonical reformulation on that owner, and
-- the chapter's owner-level `Manifold.IsImmersion.contMDiff` bridge.

universe uE uE' uH uH' uM uS

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]

/-- Corollary 6.12: if `ι : S → M` is a smooth immersion presenting an immersed
submanifold of a smooth manifold with or without boundary and the model-space dimension of `S` is
strictly smaller than that of `M`, then the immersed image `Set.range ι` has measure zero in `M`. -/
theorem range_has_measure_zero_in_manifold_of_immersion_of_model_finrank_lt
    {ι : S → M} (hιimm : IsImmersion J I ∞ ι)
    (hdim : Module.finrank ℝ E' < Module.finrank ℝ E) :
    has_measure_zero_in_manifold I (Set.range ι) :=
  range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt hιimm.contMDiff hdim

end

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]

/-- Preferred-chart formulation of Corollary 6.12, derived from the manifold owner
`has_measure_zero_in_manifold`. -/
theorem range_has_measure_zero_in_manifold_of_immersion_of_model_finrank_lt_chartwise
    {ι : S → M} (hιimm : IsImmersion J I ∞ ι)
    (hdim : Module.finrank ℝ E' < Module.finrank ℝ E) (x : M) :
    volume ((extChartAt I x) '' (Set.range ι ∩ (extChartAt I x).source)) = 0 :=
  range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt_chartwise
    hιimm.contMDiff hdim x

end
