import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_7 (from Chap09) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ψ ω : E → EReal} {σ : ℝ}

/- Lemma 9.7 is `source-facing` in the Chapter 9 mirror-descent setup. The owner abstraction for
the mirror-map assumptions is already the project class `IsBregmanPotentialOn`, instantiated on the
constraint set `dom(ψ) = effective_domain ψ`; the conclusion itself is the textbook minimizer
statement, expressed directly through mathlib's `IsMinOn` and the Chapter 3 owner
`subdifferential_domain`. -/

-- Proof sketch: use `hω.strongConvexOn_add_indicator` to view `x ↦ ψ x + ω x` as a proper closed
-- `σ`-strongly convex extended-real-valued function on `effective_domain ψ`, then apply the
-- Chapter 5 unique-minimizer theorem to obtain a unique global minimizer. For domain membership,
-- properness gives `xStar ∈ effective_domain ψ`, and Fermat's optimality condition together with
-- the convex sum rule for `ψ + ω` yields a nonempty subdifferential of `ω` at `xStar`.
/-- Lemma 9.7: if `ω` is a Bregman potential on `dom(ψ)` and `ψ` is proper, closed, and convex,
then the composite problem `min_x {ψ(x) + ω(x)}` has a unique minimizer, and that minimizer lies
in `dom(ψ) ∩ dom(∂ ω)`. -/
theorem existsUnique_composite_minimizer_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ)
    (hψ_convex : is_convex_function ψ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar ∧
        xStar ∈ effective_domain ψ ∩ subdifferential_domain ω := sorry

end

/-! ### Text_9_7 (from Chap09) -/
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
