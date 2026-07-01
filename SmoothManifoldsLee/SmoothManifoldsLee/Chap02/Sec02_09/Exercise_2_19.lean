import Mathlib.Tactic.Recall
import SmoothManifoldsLee.Chap01.Sec01_06.Theorem_1_46
import SmoothManifoldsLee.Chap02.Sec02_09.Theorem_2_18

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 2.19: use Theorem 1.46 to prove the preceding theorem. In this formalization, the
relevant source-facing bridge is `smooth_boundary_chart_frontier_independence`, and the preceding
theorem is expressed through the canonical `Diffeomorph` owner API
`Diffeomorph.image_boundary` and `Diffeomorph.restrictInterior`. -/
recall smooth_boundary_chart_frontier_independence
recall Diffeomorph.image_boundary
recall Diffeomorph.restrictInterior
