import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_38.Definition_6_38_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Manifold
open Set
open scoped ContDiff Manifold

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold`, the nearby project use of `measure_biUnion_null_iff` in
-- Proposition 6.5, and mathlib's canonical countable-family null-set lemma
-- `measure_iUnion_null`.

universe uE uH uM

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Exercise 6.7: a countable union of sets of measure zero in a smooth manifold with or without
boundary has measure zero. -/
theorem has_measure_zero_in_manifold_iUnion {ι : Sort*} [Countable ι] {s : ι → Set M}
    (hs : ∀ i, has_measure_zero_in_manifold I (s i)) :
    has_measure_zero_in_manifold I (⋃ i, s i) := by
  intro μ hμ e he
  have hzero : ∀ i, μ ((e.extend I) '' (s i ∩ e.source)) = 0 := fun i ↦ hs i μ hμ e he
  simpa [iUnion_inter, image_iUnion] using measure_iUnion_null hzero

end
