import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_2_19 (from Chap02/Sec02_09) -/
/- Exercise 2.19: use Theorem 1.46 to prove the preceding theorem. In this formalization, the
relevant source-facing bridge is `smooth_boundary_chart_frontier_independence`, and the preceding
theorem is expressed through the canonical `Diffeomorph` owner API
`Diffeomorph.image_boundary` and `Diffeomorph.restrictInterior`. -/
recall smooth_boundary_chart_frontier_independence
recall Diffeomorph.image_boundary
recall Diffeomorph.restrictInterior
