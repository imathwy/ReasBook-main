import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Exercise 4: if `f` is continuous on the closed disc `|z| ≤ r`, then the circle integrals on
the concentric circles of radii `((1 : ℝ) - 1 / (n + 1 : ℝ)) * r` converge to the circle integral
on the boundary circle of radius `r`. -/
-- Proof sketch: unfold `circleIntegral` into an interval integral over `circleMap 0 R`; then apply
-- dominated convergence on `[0, 2 * π]`, using continuity of `f` on the closed disc for the
-- pointwise limit and compactness of the closed disc for a uniform bound on the integrands.
theorem circleIntegral_tendsto_shrinking_radii_of_continuousOn_closedBall
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) r)) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∮ z in C((0 : ℂ), ((1 : ℝ) - 1 / (n + 1 : ℝ)) * r), f z)
      Filter.atTop
      (nhds (∮ z in C((0 : ℂ), r), f z)) := sorry
