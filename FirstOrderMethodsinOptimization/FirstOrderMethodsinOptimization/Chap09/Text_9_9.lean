import Mathlib
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsinOptimization.Chap09.Text_9_6
import FirstOrderMethodsinOptimization.Chap09.Text_9_7
import FirstOrderMethodsinOptimization.Chap09.Text_9_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (toLp)

/-- The Euclidean upper bound on the unit simplex used for comparison with the entropy-based
mirror-descent bound, indexed by the positive Euclidean Lipschitz constant `L_{f,2}`. -/
def simplex_euclidean_upper_bound (Lf2 : PosReal) (N : ℕ) : ℝ :=
  Real.sqrt 2 * Lf2 / Real.sqrt (N + 1 : ℝ)

/-- The non-Euclidean mirror-descent upper bound on the unit simplex with the `l_1` norm,
negative entropy mirror map, and uniform initialization `x⁰ = (1 / n)e`, indexed by the positive
sup-norm Lipschitz constant `L_{f,∞}`. -/
def simplex_non_euclidean_upper_bound (n : ℕ) (LfInf : PosReal) (N : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (n : ℝ)) * LfInf / Real.sqrt (N + 1 : ℝ)

/-- The comparison ratio of the simplex non-Euclidean and Euclidean upper bounds for a positive
sup-norm constant `L_{f,∞}` and a positive Euclidean constant `L_{f,2}`. The positivity is part
of the input type, so the quotient is a genuine ratio rather than a totalized
division-by-zero expression. -/
def simplex_efficiency_ratio (n : ℕ) (LfInf Lf2 : PosReal) : ℝ :=
  Real.sqrt (Real.log (n : ℝ)) * LfInf / Lf2

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) : Set E)

-- Proof sketch: on the simplex, the negative-entropy Bregman distance from the uniform point
-- `x⁰ = (1 / n)e` is the Kullback-Leibler divergence relative to the uniform distribution, namely
-- `∑ i x_i log (n x_i)`, and this is bounded above by `log n`.
/-- On the simplex, the negative-entropy Bregman distance to the uniform point `x⁰ = (1 / n)e`
is bounded by `log n`. This is the simplex entropy diameter estimate `Θ₀ = log n`. -/
theorem negative_entropy_bregman_le_log_of_mem_simplex
    (hn : 0 < n) {x : E} (hx : x ∈ Δ) :
    B[fun z : E ↦ negative_entropy_on_stdSimplex n z] x ((uniform_simplex_point hn : Δ) : E) ≤
      Real.log (n : ℝ) := sorry

-- Proof sketch: this is the simplex specialization of the mirror-descent fixed-horizon estimate,
-- with the feasible set `Δ_n`, mirror map the simplex negative entropy, initialization
-- `x⁰ = (1 / n)e`, entropy diameter `Θ₀ = log n`, and the source norm bound
-- `‖g_k‖_∞ ≤ L_{f,∞}` encoded by `‖toLp ⊤ (g k)‖ ≤ LfInf`. The required optimizer witness is
-- chosen internally from `h_problem.optimal_set_nonempty`.
/-- The simplex negative-entropy mirror-descent estimate before optimizing the constant stepsize:
if the chosen simplex mirror-descent trajectory starts at `x⁰ = (1 / n)e` and its selected
subgradients satisfy `‖g_k‖_∞ ≤ L_{f,∞}` on the first `N + 1` iterations, then the running-best
objective value gap is bounded by the fixed-iteration mirror-descent objective with
`Θ₀ = log n` and `σ = 1`. -/
theorem simplex_negative_entropy_best_value_gap_le_fixed_iteration_objective
    (hn : 0 < n) {f : E → EReal} {XStar : Set E} {fOpt LfInf : ℝ}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y : E ↦ (negative_entropy_on_stdSimplex n y).toReal)
        Δ x g t)
    (hx0 : x 0 = ((uniform_simplex_point hn : Δ) : E))
    {N : ℕ}
    (h_subgrad_bound :
      ∀ k : Fin (N + 1), ‖toLp ⊤ (fun i ↦ g k i)‖ ≤ LfInf) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      fixed_iteration_objective (Real.log (n : ℝ)) (LfInf ^ 2 / 2) (fun k : Fin (N + 1) ↦ t k) :=
  sorry

-- Proof sketch: combine
-- `simplex_negative_entropy_best_value_gap_le_fixed_iteration_objective` with the constant-step
-- specialization `t_k = √(2 log n) / (L_{f,∞} √(N + 1))`, using Text 9.7 only as the internal
-- bridge back to the core owner `fixed_iteration_uniform_steps`. The optimizer witness is chosen
-- internally from `h_problem.optimal_set_nonempty`. The assumption `1 < n` gives `0 < log n`,
-- and positivity of `L_{f,∞}` is carried by `PosReal`. Simplifying the fixed-iteration value then
-- yields the owner definition `simplex_non_euclidean_upper_bound`.
/-- Text 9.9 (1): for mirror descent on the unit simplex `Δ_n` with the `l_1` norm, negative
entropy mirror map, uniform initialization `x⁰ = (1 / n)e`, and positive sup-norm Lipschitz
constant `L_{f,∞}`, the optimal constant stepsizes from Text 9.7 give the running-best objective
value gap bound `√(2 log n) L_{f,∞} / √(N + 1)` when `1 < n`. -/
theorem simplex_negative_entropy_best_value_gap_le_non_euclidean_upper_bound
    {f : E → EReal} {XStar : Set E} {fOpt : ℝ} {LfInf : PosReal}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    {x g : ℕ → E} {t : ℕ → ℝ}
    (h_traj :
      is_mirror_descent_trajectory
        (fun y ↦ (f y).toReal)
        (fun y : E ↦ (negative_entropy_on_stdSimplex n y).toReal)
        Δ x g t)
    {N : ℕ}
    (h_subgrad_bound :
      ∀ k : Fin (N + 1), ‖toLp ⊤ (fun i ↦ g k i)‖ ≤ (LfInf : ℝ))
    (hn : 1 < n)
    (hx0 : x 0 = ((uniform_simplex_point (Nat.zero_lt_of_lt hn) : Δ) : E))
    (h_stepsize :
      ∀ k : Fin (N + 1),
        t k =
          Real.sqrt (2 * Real.log (n : ℝ)) /
            ((LfInf : ℝ) * Real.sqrt (N + 1 : ℝ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      simplex_non_euclidean_upper_bound n LfInf N := sorry

end

-- Proof sketch: expand the three owner definitions, cancel the common factor
-- `√2 / √(N + 1)`, and simplify the quotient of the two upper bounds to
-- `√(log n) * LfInf / Lf2`.
/-- The efficiency ratio agrees with the quotient of the named non-Euclidean and Euclidean upper
bound constants. -/
theorem simplex_efficiency_ratio_eq_upper_bound_ratio
    (n : ℕ) (LfInf Lf2 : PosReal) (N : ℕ) :
    simplex_efficiency_ratio n LfInf Lf2 =
      simplex_non_euclidean_upper_bound n LfInf N /
        simplex_euclidean_upper_bound Lf2 N := sorry

-- Proof sketch: rewrite the ratio using `simplex_efficiency_ratio_eq_upper_bound_ratio` and the
-- explicit formula `ρ = √(log n) * (L_{f,∞} / L_{f,2})`. Then apply the standard norm-comparison
-- consequences `L_{f,∞} ≤ L_{f,2} ≤ √n L_{f,∞}` to bound the quotient `L_{f,∞} / L_{f,2}`
-- between `1 / √n` and `1`.
/-- Text 9.9 (2): if the Euclidean and sup-norm Lipschitz constants satisfy
`L_{f,∞} ≤ L_{f,2} ≤ √n L_{f,∞}`, then the comparison ratio of the non-Euclidean and Euclidean
upper bounds lies between `√(log n) / √n` and `√(log n)`. -/
theorem simplex_efficiency_ratio_bounds
    (n : ℕ) (LfInf Lf2 : PosReal)
    (h_upper : (LfInf : ℝ) ≤ (Lf2 : ℝ))
    (h_lower : (Lf2 : ℝ) ≤ Real.sqrt (n : ℝ) * (LfInf : ℝ)) :
    Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) ≤ simplex_efficiency_ratio n LfInf Lf2 ∧
      simplex_efficiency_ratio n LfInf Lf2 ≤ Real.sqrt (Real.log (n : ℝ)) := sorry
