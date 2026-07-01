import FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsinOptimization.Chap09.Definition_9_4
import FirstOrderMethodsinOptimization.Chap09.Definition_9_5
import FirstOrderMethodsinOptimization.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt Lf σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the relevant API guidance comes from the local
Chapter 8 and Chapter 9 owner files. Theorem 9.27 is `source-facing`: it gives the dynamic-step
`O(log k / √k)` rate for the concrete Mirror-C trajectory from Definition 9.6 under the composite
problem assumptions of Definition 9.4 and the Bregman-potential assumptions of Definition 9.5.
The canonical owners already present are the trajectory predicate `is_mirror_c_trajectory`, the
running-best value `best_achieved_function_value`, the composite-problem package
`IsCompositeMirrorDescentProblem`, and the Bregman distance owner `B[ω]`. -/

-- Proof sketch: apply the one-step dynamic-stepsize estimate from Lemma 9.25 to an optimal point
-- `xStar ∈ XStar`, rewrite `t n` using the prescribed rule
-- `√(2 σ) / (L_f √(n + 1))`, and use the problem's subgradient bound `‖f'(x^n)‖_* ≤ L_f` to
-- convert the numerator correction term into the harmonic sum `∑_{n=0}^k 1 / (n + 1)`. The
-- resulting ratio is exactly the prefix ratio controlled by Lemma 8.27 (1).
/-- Theorem 9.27: under the composite mirror-descent assumptions of Definitions 9.4, 9.5, and
9.6, if `g` is nonnegative on `dom(g)` and the Mirror-C stepsizes are chosen by
`t_k = √(2 σ) / (L_f √(k + 1))`, then for every `k ≥ 1` the running-best composite objective gap
is bounded by the `O(log k / √k)` estimate
`(L_f / √(2 σ)) * (B[ω] xStar x⁰ + (√(2 σ) / L_f) g(x⁰) + 1 + log (k + 1)) / √(k + 1)`. -/
theorem mirror_c_best_value_gap_le_log_over_sqrt_of_dynamic_stepsizes
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize :
      ∀ n, t n = Real.sqrt (2 * σ) / (Lf * Real.sqrt ((n : ℝ) + 1))) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt ≤
      (Lf / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) +
          (Real.sqrt (2 * σ) / Lf) * (g (x 0)).toReal +
          1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := sorry

end
