import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BoundedContinuousFunction CompactlySupported

/-- Exercise 13.1.1 (1): the supremum-norm space `C([0,1], ℝ)` is separable. -/
-- This is the canonical owner instance for continuous maps on a locally compact second-countable
-- domain.
theorem continuousMap_Icc_zero_one_separable :
    TopologicalSpace.SeparableSpace (C(Set.Icc (0 : ℝ) 1, ℝ)) := by
  infer_instance

/-- Exercise 13.1.1 (2): the supremum-norm space of bounded continuous real-valued functions on
`[0, ∞)` is not separable. -/
-- Proof sketch: produce an uncountable family of bounded continuous functions that are pairwise
-- separated by a fixed positive distance in the supremum norm.
theorem boundedContinuousFunction_Ici_not_separable :
    ¬ TopologicalSpace.SeparableSpace ((Set.Ici (0 : ℝ)) →ᵇ ℝ) := sorry

/-- Exercise 13.1.1 (3): the supremum-norm space `C_c([0, ∞), ℝ)` is separable. -/
-- This is the canonical owner instance for compactly supported continuous maps on a locally
-- compact second-countable domain.
theorem compactlySupportedContinuousMap_Ici_separable :
    TopologicalSpace.SeparableSpace (C_c(Set.Ici (0 : ℝ), ℝ)) := by
  infer_instance
