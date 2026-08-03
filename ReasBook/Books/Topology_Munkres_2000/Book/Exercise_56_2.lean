module

public import Topology_Munkres_2000.Book.Exercise_56_1.Complexification

open Polynomial
open scoped BigOperators

public section

/-- Exercise 56.2: The open disk of radius `2` about the origin contains every
root of the equation `x ^ 7 + x ^ 2 + 1 = 0`. -/
theorem rootsOfXSeventhAddXSquareAddOne_mem_ball (z : ℂ)
    (hz : z ^ 7 + z ^ 2 + 1 = 0) : z ∈ Metric.ball 0 2 := by
  let p : Polynomial ℂ := X ^ 7 + (C (1 / 32) * X ^ 2 + C (1 / 128))
  have hp : p.Monic := by
    dsimp [p]
    apply monic_X_pow_add
    calc
      (C (1 / 32) * X ^ 2 + C (1 / 128) : Polynomial ℂ).degree
          ≤ max (C (1 / 32) * X ^ 2 : Polynomial ℂ).degree
              (C (1 / 128)).degree := degree_add_le _ _
      _ ≤ max 2 0 :=
        max_le (degree_C_mul_X_pow_le 2 (1 / 32)) (degree_C_le.trans (le_max_right _ _))
      _ < 7 := by norm_num
  have hcoeff : (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖) < 1 := by
    dsimp [p]
    norm_num [Finset.sum_range_succ, natDegree_add_eq_left_of_natDegree_lt,
      natDegree_C_mul_X_pow]
  have hy : p.IsRoot (z / 2) := by
    rw [IsRoot.def]
    dsimp [p]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    calc
      (z / 2) ^ 7 + (1 / 32 * (z / 2) ^ 2 + 1 / 128) =
          (z ^ 7 + z ^ 2 + 1) / 128 := by ring
      _ = 0 := by rw [hz]; norm_num
  have hy_norm : ‖z / 2‖ < 1 :=
    hy.norm_lt_one_of_monic_of_sum_norm_lt_one p hp hcoeff
  rw [Metric.mem_ball, dist_zero_right]
  norm_num [norm_div] at hy_norm ⊢
  linarith

end
