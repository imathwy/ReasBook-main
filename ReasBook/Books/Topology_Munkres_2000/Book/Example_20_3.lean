module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- Example 20.3 (1): In dimension one, Euclidean distance is the standard
distance on the unique real coordinate. -/
lemma euclideanDist_finOne (x y : EuclideanSpace ℝ (Fin 1)) :
    dist x y = dist (x 0) (y 0) := by
  -- The Euclidean formula reduces to the unique coordinate.
  simp [EuclideanSpace.dist_eq]

/-- Helper for Example 20.3: In dimension one, the coordinatewise maximum distance is
the standard distance on the unique real coordinate. -/
lemma squareDist_finOne (x y : Fin 1 → ℝ) :
    dist x y = dist (x 0) (y 0) := by
  -- The supremum over `Fin 1` is the value at its unique coordinate.
  simp [dist_pi_def, Finset.univ_unique, Finset.sup_singleton]

/-- Helper for Example 20.3: Open Euclidean balls in the plane are circular regions,
described by the sum-of-squares inequality. -/
lemma euclideanBall_finTwo (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r =
      {y | dist (y 0) (x 0) ^ 2 + dist (y 1) (x 1) ^ 2 < r ^ 2} := by
  -- Membership may be squared because both sides of the inequality are nonnegative.
  ext y
  rw [Metric.mem_ball, Set.mem_setOf_eq, ← sq_lt_sq₀ dist_nonneg hr.le]
  -- The squared Euclidean distance is the two-coordinate sum of squares.
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]

/-- Helper for Example 20.3: Open balls for the coordinatewise maximum metric in the
plane are axis-aligned open square regions. -/
lemma squareBall_finTwo (x : Fin 2 → ℝ) (r : ℝ) :
    Metric.ball x r =
      {y | dist (y 0) (x 0) < r ∧ dist (y 1) (x 1) < r} := by
  -- Product balls impose the ball inequality independently in each coordinate.
  rw [ball_pi']
  ext y
  simp only [Set.mem_pi, Set.mem_univ, Metric.mem_ball, forall_const, Set.mem_setOf_eq,
    Fin.forall_fin_two]
