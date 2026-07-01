import Mathlib
import FirstOrderMethodsinOptimization.Chap08.Assumption_8_12
import FirstOrderMethodsinOptimization.Chap08.Definition_8_8
import FirstOrderMethodsinOptimization.Chap09.Definition_9_1
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsinOptimization.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

-- Proof sketch: combine the one-step mirror-descent inequality from the prox theorem with convexity
-- of `(fun y ↦ (f y).toReal)` to obtain a one-step bound
-- `t k * ((f (x k)).toReal - fOpt) ≤ B_ω(xStar, x k) - B_ω(xStar, x (k + 1)) +
--   (t k)^2 * h_bound.L_f^2 / (2 * σ)` for an optimal point `xStar ∈ XStar`. Sum from `k = 0`
-- to `N`, use the subgradient norm bound packaged by `h_bound`, telescope the Bregman terms, and
-- compare the weighted sum of objective gaps with the prefix minimum
-- `best_achieved_function_value (fun y ↦ (f y).toReal) x N`.
/-- Lemma 9.14: under Definition 9.1 for the constrained problem `min {f(x) : x ∈ C}` and
Definition 9.2 for the mirror potential `ω`, if every subgradient of `f` on `C` has norm at most
`L_f = h_bound.L_f`, then for every optimal point `xStar ∈ XStar`, every mirror-descent
trajectory `x` with positive stepsizes `t`, and every `N`, the running-best objective gap
satisfies
`f_best^N - f_opt ≤ (B_ω(xStar, x⁰) + (h_bound.L_f^2 / (2σ)) * ∑_{k=0}^N t_k^2) / ∑_{k=0}^N t_k`. -/
theorem mirror_descent_best_value_gap_le
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    (N : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      (B[ω] xStar (x 0) +
          (h_bound.L_f ^ (2 : ℕ) / (2 * σ)) *
            Finset.sum (Finset.range (N + 1)) (fun k ↦ (t k) ^ (2 : ℕ))) /
        Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := sorry

end
