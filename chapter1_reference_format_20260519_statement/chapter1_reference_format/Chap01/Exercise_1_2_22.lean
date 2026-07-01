import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Metric IsUltrametricDist

variable {p : ℕ} [Fact p.Prime]

-- Proof sketch: specialize `IsUltrametricDist.ball_eq_of_mem` to the ultrametric space `ℚ_[p]`.
/-- Exercise 1.2.22 (1): in `ℚ_[p]`, every point of an open ball is also a center of that ball. -/
theorem padic_openBall_eq_of_mem {α β : ℚ_[p]} {r : ℝ} (h : β ∈ ball α r) :
    ball β r = ball α r := by
  simpa using (ball_eq_of_mem h).symm

-- Proof sketch: specialize `IsUltrametricDist.closedBall_eq_of_mem` to `ℚ_[p]`.
/-- Exercise 1.2.22 (2): in `ℚ_[p]`, every point of a closed ball is also a center of that ball. -/
theorem padic_closedBall_eq_of_mem {α β : ℚ_[p]} {r : ℝ} (h : β ∈ closedBall α r) :
    closedBall β r = closedBall α r := by
  simpa using (closedBall_eq_of_mem h).symm

-- Proof sketch: if two side lengths are unequal, `IsUltrametricDist.dist_eq_max_of_dist_ne_dist`
-- forces the third side to equal the larger one; a case split on equalities yields two equal sides.
/-- Exercise 1.2.22 (3): every triangle in `ℚ_[p]` is isosceles, meaning that two of its side
lengths coincide. -/
theorem padic_triangle_isosceles (x y z : ℚ_[p]) :
    dist x y = dist y z ∨ dist y z = dist z x ∨ dist z x = dist x y := by
  by_cases hxy : dist x y = dist y z
  · exact Or.inl hxy
  · have hxz := dist_eq_max_of_dist_ne_dist x y z hxy
    rcases lt_or_gt_of_ne hxy with hxy | hxy
    · exact Or.inr <| Or.inl <| by
        simpa [max_eq_right hxy.le, dist_comm] using hxz.symm
    · exact Or.inr <| Or.inr <| by
        simpa [max_eq_left hxy.le, dist_comm] using hxz
