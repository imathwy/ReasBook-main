import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Lemma_9_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Text 9.7 is `bridge/view`: the chapter owner for the constant minimizing step family is already
`fixed_iteration_uniform_steps` from Lemma 9.15. This file keeps the mirror-descent specialization
and the textbook closed forms, but does not introduce a second owner for the same family. -/

-- Proof sketch: specialize `fixed_iteration_uniform_steps_apply` to `ι = Fin (N + 1)` and
-- `β = Lf ^ 2 / (2 * σ)`, then use positivity of `Lf` to rewrite the resulting
-- `|Lf|` denominator as `Lf`, obtaining the textbook constant stepsize
-- `√(2 * Theta0 * σ) / (Lf * √(N + 1))`.
/-- For positive `Theta0`, `Lf`, and `σ`, specializing the Lemma 9.15 uniform minimizer to the
mirror-descent coefficients gives the textbook constant stepsize
`√(2 * Theta0 * σ) / (Lf * √(N + 1))`. -/
theorem fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
    (Theta0 Lf σ : ℝ) (N : ℕ)
    (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) =
      fun _ ↦ Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N + 1 : ℝ)) := sorry

-- Proof sketch: use positivity of `Theta0`, `Lf`, and `σ` together with positivity of
-- `Real.sqrt` on positive inputs to show that the displayed constant is positive.
/-- The optimal constant stepsize from Text 9.7 is positive at every iteration index when
`Theta0`, `Lf`, and `σ` are positive. -/
theorem mirror_descent_optimal_constant_stepsize_pos
    (Theta0 Lf σ : ℝ) (N : ℕ) (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    ∀ i : Fin (N + 1),
      0 < fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) i := sorry

-- Proof sketch: apply `fixed_iteration_objective_minimized_by_uniform_steps` and
-- `fixed_iteration_objective_uniform_step_value` from Lemma 9.15 with
-- `α = Theta0`, `β = Lf ^ 2 / (2 * σ)`, and `ι = Fin (N + 1)`, then simplify the uniform
-- optimizer to the textbook formula `√(2 * Theta0 * σ) / (Lf * √(N + 1))`.
/-- Text 9.7: with `α = Theta0`, `β = Lf ^ 2 / (2 * σ)`, and `m = N + 1`, the mirror-descent
fixed-iteration bound is minimized by the constant stepsize
`√(2 * Theta0 * σ) / (Lf * √(N + 1))`, and the attained value is
`Lf * √(2 * Theta0) / √(σ * (N + 1))`, which is the explicit `O(1 / √N)` bound. -/
theorem mirror_descent_optimal_constant_stepsize_minimizes_fixed_iteration_bound
    (Theta0 Lf σ : ℝ) (N : ℕ) (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    IsMinOn (fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ)))
        {t : Fin (N + 1) → ℝ | ∀ i, 0 < t i}
        (fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ))) ∧
      fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ))
          (fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ))) =
        Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := sorry

end
