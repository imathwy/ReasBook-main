import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The cubic map on `ℝ` used for Lee's alternate one-chart smooth structure. -/
def cubicMap : ℝ → ℝ :=
  fun x ↦ x ^ (3 : ℕ)
