module

public import Mathlib.Analysis.Normed.Lp.PiLp

public section

/- Exercise 20.1 (1): The ℓ¹ distance on `PiLp 1 (fun _ : Fin n ↦ ℝ)` is a metric,
and its topology is the usual finite-product topology. -/
#check fun n : ℕ ↦ (inferInstance : MetricSpace (PiLp 1 (fun _ : Fin n ↦ ℝ)))
#check PiLp.dist_eq_of_L1
#check PiLp.homeomorph

/-- Exercise 20.1 (2): In two dimensions, the open balls for the ℓ¹ metric are open
diamonds described by the sum of the two coordinate differences. -/
theorem l1Ball_finTwo (x : PiLp 1 (fun _ : Fin 2 ↦ ℝ)) (r : ℝ) :
    Metric.ball x r = {y | |y 0 - x 0| + |y 1 - x 1| < r} := by
  ext y
  simp [Metric.mem_ball, PiLp.dist_eq_of_L1, Fin.sum_univ_two, Real.dist_eq]

/- Exercise 20.1 (3): For finite `p ≥ 1`, the canonical ℓᵖ distance has the coordinate-sum
formula and induces the usual finite-product topology. -/
#check PiLp.dist_eq_sum
#check PiLp.homeomorph
