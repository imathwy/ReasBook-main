import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Lemma_9_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt Lf σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the relevant API guidance comes from the existing
Chapter 8 and Chapter 9 owner files. Theorem 9.26 is `source-facing`: it states the fixed-horizon
`O(1 / √N)` rate for a concrete Mirror-C trajectory. The canonical owners already present are the
composite-problem package `IsCompositeMirrorDescentProblem`, the Bregman-potential package
`IsBregmanPotentialOn`, the trajectory predicate `is_mirror_c_trajectory`, the Bregman distance
`B[ω]`, the running-best value owner `best_achieved_function_value`, and the finite-horizon
constant-step family `fixed_iteration_uniform_steps`. The textbook closed form for the stepsizes is
derived from that owner, so it should not remain primitive input data here. -/

-- Proof sketch: apply the fixed-horizon estimate from Lemma 9.25 to a chosen optimal point
-- `xStar ∈ XStar`, use the pointwise Bregman upper bound
-- `B[ω](xStar, x 0) ≤ Theta0`, the initial-feasibility condition `g (x 0) = 0`, and the
-- canonical finite-horizon constant-step family
-- `fixed_iteration_uniform_steps (Fin N) Theta0 (Lf ^ 2 / (2 * σ))`, whose closed form is
-- `√(2 * Theta0 * σ) / (Lf * √N)`. Simplifying the resulting ratio gives the standard
-- `Lf * √(2 * Theta0) / (√σ * √N)` bound for the running best objective value.
/-- Theorem 9.26: under the standing composite mirror-descent assumptions of Definition 9.4
together with Definitions 9.5 and 9.6, if `g` is nonnegative on `dom(g)`, if some optimizer
`xStar ∈ X^*` satisfies `B[ω](xStar, x⁰) ≤ Theta0`, if `g(x⁰) = 0`, and if the first `N` Mirror-C
stepsizes are given by the canonical finite-horizon uniform family from Lemma 9.15,
equivalently by the textbook constant value `√(2 * Theta0 * σ) / (Lf * √N)`, then after `N`
iterations the best objective value attained among `x⁰, …, x^(N-1)` satisfies the fixed-horizon
`O(1 / √N)` estimate. -/
theorem mirror_c_best_value_gap_le_one_div_sqrt_of_constant_stepsizes
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_g0 : g (x 0) = 0)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ} (hN : 0 < N)
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      ∀ n : Fin N, t n = fixed_iteration_uniform_steps (Fin N) Theta0 (Lf ^ 2 / (2 * σ)) n) :
    best_achieved_function_value (fun y : E ↦ (f y + g y).toReal) x (N - 1) - FOpt ≤
      Lf * Real.sqrt (2 * Theta0) / (Real.sqrt σ * Real.sqrt (N : ℝ)) := sorry

end
