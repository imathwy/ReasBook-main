import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_38.Definition_6_38_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ContDiff Manifold

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold` together with the nearby canonical APIs
-- `has_measure_zero_in_manifold_iUnion`,
-- `has_measure_zero_in_manifold.dense_compl`, and
-- `has_measure_zero_in_manifold.image_of_contMDiff`.
-- Those declarations all treat manifold-null sets through the single owner
-- `has_measure_zero_in_manifold`, so Definition 6.44-extra-3 is a source-facing complement view
-- of that owner rather than a second predicate.

universe uE uH uM

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {B : Set M}

/- Definition 6.44-extra-3: a subset `B ⊆ M` contains almost every element of the smooth manifold
`M` exactly when its complement has measure zero in `M`. This is the complement presentation of
the Section 6.38 owner `has_measure_zero_in_manifold`, not a second owner abstraction. -/
#check (has_measure_zero_in_manifold I Bᶜ)

end
