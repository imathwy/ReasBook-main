import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- Lemma 9.13 is `source-facing`: it is the one-step mirror-descent descent estimate for a concrete
trajectory. The chapter already has the right owners for each ingredient:
- `IsConstrainedConvexProblem` for Definition 9.1,
- `IsBregmanPotentialOn` and `B[ω]` for Definition 9.2,
- `is_mirror_descent_trajectory` for the generated iterates,
- `bregman_three_point_identity` and Theorem 9.12 as the canonical proof route.
No extra wrapper around the step inequality is mathematically justified here. -/

-- Proof sketch: specialize the trajectory update at step `k`, then apply Theorem 9.12 to the
-- second-prox objective obtained from the linear term `t k • g k` and the feasible-set indicator.
-- Rewrite the resulting optimality inequality with `bregman_three_point_identity`, bound the
-- intermediate Bregman term below by `σ / 2 * ‖x (k + 1) - x k‖^2`, and absorb the mixed term by
-- the Euclidean Young/Fenchel inequality. Finally substitute `u = xStar` and use optimality of
-- `xStar ∈ XStar` together with the subgradient inequality for `g k`.
/-- Lemma 9.13: under the standing constrained-problem assumptions of Definition 9.1 and the
Bregman-potential assumptions of Definition 9.2, every step of a mirror-descent trajectory
satisfies the fundamental inequality
`t_k (f(x^k).toReal - f_opt) ≤ B_ω(xStar, x^k) - B_ω(xStar, x^(k+1)) + t_k^2 ‖g_k‖^2 / (2σ)` for
each optimal point `xStar ∈ XStar`. -/
theorem mirror_descent_fundamental_inequality
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    t k * ((f (x k)).toReal - fOpt) ≤
      B[ω] xStar (x k) - B[ω] xStar (x (k + 1)) +
        (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) := sorry

end
