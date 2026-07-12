import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

-- Semantic Lean search tool unavailable in this environment; verified against mathlib's
-- `MeasureTheory.addHaar_affineSubspace` and specialized here to `ℝ^n`.

/-- Corollary 6.4: every proper affine subspace of `ℝ^n` has measure zero in `ℝ^n`. -/
theorem volume_affineSubspace_eq_zero_of_ne_top {n : ℕ}
    (s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) (hs : s ≠ ⊤) :
    volume (s : Set (EuclideanSpace ℝ (Fin n))) = 0 := by
  -- Specialize the general Haar-measure vanishing theorem to `volume` on `ℝ^n`.
  simpa using Measure.addHaar_affineSubspace volume s hs
