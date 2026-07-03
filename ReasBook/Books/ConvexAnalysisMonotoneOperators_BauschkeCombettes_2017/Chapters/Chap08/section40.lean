import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_40 (from Chap08) -/
universe u

-- Proof sketch: apply the finite-dimensional continuity theorem for convex functions on `Set.univ`,
-- for instance by first obtaining local Lipschitz continuity from `ConvexOn.locallyLipschitz` and
-- then deducing continuity from `LocallyLipschitz.continuous`.
/-- Corollary 8.40: every convex real-valued function on a finite-dimensional real Hilbert space is
continuous. -/
theorem continuous_of_convexOn_univ
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (f : H → ℝ) (hconv : ConvexOn ℝ Set.univ f) :
    Continuous f := by
  -- Finite-dimensional convexity gives the local Lipschitz control that underlies the textbook
  -- continuity argument.
  have hloc : LocallyLipschitz f := hconv.locallyLipschitz
  -- A locally Lipschitz map is continuous.
  exact hloc.continuous
