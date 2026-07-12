import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MeasureTheory
open scoped ENNReal

section

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

#check ContinuousMap.toLp
#check ContinuousMap.toLp_denseRange
#check (ContinuousMap.toLp_denseRange (α := G) (E := ℂ)
  (μ := (normalizedHaarMeasure : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ))
#check (show DenseRange (ContinuousMap.toLp (α := G) (E := ℂ) (p := (2 : ENNReal))
  (μ := (normalizedHaarMeasure : Measure G)) (𝕜 := ℂ)) from
  ContinuousMap.toLp_denseRange (α := G) (E := ℂ)
    (μ := (normalizedHaarMeasure : Measure G)) (p := (2 : ENNReal)) (𝕜 := ℂ)
    (by norm_num : (2 : ENNReal) ≠ ∞))

end