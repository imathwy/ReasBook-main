import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Proof sketch: for the forward implication, tightness gives uniform control of Gaussian tails,
-- which forces uniform bounds on both the means and variances. For the reverse implication, a
-- bounded parameter set yields a common compact interval capturing arbitrarily large mass for all
-- Gaussian laws in the family.
/- Exercise 13.3.2 is `source-facing` in the tightness/weak-convergence domain. Its primitive
data are the Gaussian mean and strictly positive variance parameters, while the `core/canonical`
owner abstractions are `ProbabilityTheory.gaussianReal` for the laws and
`MeasureTheory.IsTightMeasureSet` for family tightness. Using `Set.Ioi (0 : ℝ≥0)` keeps strict
positivity as primitive data in the owner parameter type, so the family can be expressed directly
as `p ↦ gaussianReal p.1 p.2` instead of via the bridge `Real.toNNReal`. -/
/-- Exercise 13.3.2: the family of normal distributions with parameter set `L ⊆ ℝ × (0, ∞)` is
tight if and only if the parameter set `L` is bounded. -/
theorem isTightMeasureSet_gaussianReal_image_iff_isBounded
    (L : Set (ℝ × Set.Ioi (0 : ℝ≥0))) :
    IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L) ↔
      Bornology.IsBounded L := sorry
