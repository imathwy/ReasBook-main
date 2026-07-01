import Mathlib
import FirstOrderMethodsinOptimization.Chap09.Text_9_2

-- Declarations for this item will be appended below by the statement pipeline.
/- Text 9.3 is `source-facing`: it asserts the existence of a strictly convex real-valued
generator together with positive points witnessing triangle-inequality failure. The core owner is
the Chapter 9 Bregman distance `bregmanDistance`; the one-dimensional bridge to real-valued
generators is already supplied upstream in `Text_9_2`, so this file keeps the witness data itself
rather than repackaging it as an auxiliary set. -/

/-- The cubic generator used to witness failure of the triangle inequality for Bregman distance. -/
def cubic_bregmanGenerator : ℝ → ℝ :=
  fun x ↦ x ^ (3 : ℕ)

/-- Evaluating the cubic Bregman generator. -/
@[simp] theorem cubic_bregmanGenerator_apply (x : ℝ) :
    cubic_bregmanGenerator x = x ^ (3 : ℕ) :=
  rfl

-- Proof sketch: apply the one-variable strict-convexity criterion on `(0, ∞)` to `x ↦ x^3`,
-- using that its second derivative is positive there.
/-- The cubic generator is strictly convex on the positive real line. -/
theorem strictConvexOn_cubic_bregmanGenerator :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) cubic_bregmanGenerator := sorry

-- Proof sketch: compute the three Bregman distances for `ω(x) = x^3` at `x = 3`, `y = 2`,
-- and `z = 1`; the values are `20`, `7`, and `4`, so the direct distance exceeds the broken path.
/-- The cubic generator violates the triangle inequality at the points `3`, `2`, and `1`. -/
theorem cubic_bregman_triangle_counterexample :
    B[cubic_bregmanGenerator] 3 1 >
      B[cubic_bregmanGenerator] 3 2 + B[cubic_bregmanGenerator] 2 1 := sorry

-- Proof sketch: witness the existential statement with `ω(x) = x^3` on `(0, ∞)` and the points
-- `x = 3`, `y = 2`, `z = 1`, combining strict convexity with the explicit counterexample above.
/-- Text 9.3: the Bregman distance need not satisfy the triangle inequality; a strictly convex
generator on the positive reals already gives a counterexample. -/
theorem exists_strictly_convex_bregman_triangle_counterexample :
    ∃ ω : ℝ → ℝ,
      StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) ω ∧
        ∃ x y z : ℝ,
          0 < x ∧
            0 < y ∧
              0 < z ∧
                B[ω] x z > B[ω] x y + B[ω] y z := sorry
