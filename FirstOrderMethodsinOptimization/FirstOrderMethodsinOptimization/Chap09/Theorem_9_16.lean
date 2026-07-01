import FirstOrderMethodsinOptimization.Chap08.Assumption_8_7
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsinOptimization.Chap09.Definition_9_3
import FirstOrderMethodsinOptimization.Chap09.Text_9_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the API review is based on the existing Chapter 8
and Chapter 9 owner files. Theorem 9.16 is `source-facing`: it gives the fixed-horizon
`O(1 / √N)` running-best gap estimate for a concrete mirror-descent trajectory under the standing
constrained-problem assumptions of Definition 9.1, the Bregman-potential assumptions of Definition
9.2, and a uniform subgradient norm bound. The canonical owners already present are
`IsConstrainedConvexProblem`, `IsBregmanPotentialOn`, `SubgradientNormBoundOn`,
`is_mirror_descent_trajectory`, `B[ω]`, `best_achieved_function_value`, and the specialized
constant-step owner `fixed_iteration_uniform_steps`. -/

-- Proof sketch: start from the fixed-horizon mirror-descent estimate from Lemma 9.14, apply it to
-- the chosen optimizer `xStar ∈ XStar`, and bound the Bregman term by `Theta0` using
-- `h_bregman_upper`. The
-- subgradient correction term is controlled by `h_bound.norm_le`, and substituting the constant
-- schedule from Text 9.7 reduces the resulting ratio to the explicit `O(1 / √N)` expression.
/-- Theorem 9.16: under the standing constrained-problem assumptions of Definition 9.1 and the
Bregman-potential assumptions of Definition 9.2, if every subgradient of `f` on `C` has norm at
most `L_f = h_bound.L_f`, if some optimizer `xStar ∈ X^*` satisfies
`B_ω(xStar, x⁰) ≤ Theta0`, and if the mirror descent stepsizes are fixed to
`√(2 * Theta0 * σ) / (L_f * √(N + 1))` on the first `N + 1` iterations, then the running-best
objective gap after `N` iterations is bounded by the standard `O(1 / √N)` estimate. -/
theorem mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ}
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      ∀ n : Fin (N + 1),
        t n =
          fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (h_bound.L_f ^ 2 / (2 * σ)) n) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      h_bound.L_f * Real.sqrt (2 * Theta0) / Real.sqrt (σ * ((N : ℝ) + 1)) := sorry

end
