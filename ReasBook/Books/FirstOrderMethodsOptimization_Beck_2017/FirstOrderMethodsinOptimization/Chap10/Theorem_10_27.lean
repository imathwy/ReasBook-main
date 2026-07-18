import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Lemma_10_12
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Theorem_10_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {Lf : NNReal}
variable {x : ℕ → E} {L : ℕ → PosReal}

/- Theorem 10.27 is `source-facing` in the Chapter 10 proximal-gradient rate API.

Domain sampling in the surrounding chapter identifies:
- `G[L; f, g]` from Definition 10.5 as the source-facing notation for the canonical owner
  `gradient_mapping` for a real-valued smooth term;
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 as the source-facing owner of the
  exact constant stepsize regime `L_k = L_f`;
- `prox_grad_step_gradient_mapping_norm_monotone` from Lemma 10.12 as the one-step monotonicity
  bridge;
- `IsConvexCompositeSmoothMinimizationProblem f.toExtendedReal g XStar FOpt Lf` as the convex Chapter 10
  owner needed only for the optimizer-dependent sublinear-rate clause (b);
- `proximal_gradient_best_gradient_mapping_norm_le_sublinear_rate` from Theorem 10.26 as the
  running-minimum `O(1 / k)` rate owner.

Triage for this file:
- `source-facing`: the two residual-rate clauses of Theorem 10.27;
- `core/canonical`: `gradient_mapping` for the residual itself, together with the convex composite
  Chapter 10 owner only where optimizer data is genuinely needed;
- `bridge/view`: the positive constant stepsize parameter `hLconst.stepsize` derived from the
  exact rule `L_k = L_f`.

Primitive data for clause (a) are the convexity and global `L_f`-smoothness of `f`, the
proper/closed/convex regularity of `g`, the trajectory, and the exact constant-rule owner from
Remark 10.19; optimizer-set data are irrelevant there and should not survive on the public API.
Clause (b) is different: it uses the Chapter 10 sublinear-rate owner from Theorem 10.26, so the
optimizer set and value remain part of that clause through
  `IsConvexCompositeSmoothMinimizationProblem`. The residual itself still belongs on the
  source-facing owner surface `G[L; f, g]`; the problem owner contributes only the optimizer data
  and the canonical `g`-regularity instances needed to elaborate that owner, not a second
  mathematical residual owner. -/

-- Proof sketch: apply Lemma 10.12 at the iterate `x^k` using the primitive convexity and global
-- `L_f`-smoothness hypotheses on `f` together with the ambient proper/closed/convex regularity of
-- `g`. The trajectory rule together with
-- `uses_proximal_gradient_Lf_stepsize_rule Lf L` identifies the prox-gradient step
-- `T_(L_f)(x^k)` with the next iterate `x^(k+1)`. The public source-facing parameter
-- `hLconst.stepsize` upgrades `L_f` to the positive parameter required by `G[L; f, g]`.
/-- Theorem 10.27 (1): clause (a). If `g` is proper, closed, and convex, `f` is convex and
globally `L_f`-smooth, and the proximal-gradient trajectory uses the constant stepsize rule
`L_k = L_f`, then the gradient-mapping norms are nonincreasing:
`‖G_(L_f)(x^(k+1))‖ ≤ ‖G_(L_f)(x^k)‖`. -/
theorem proximal_gradient_mapping_norm_nonincreasing_of_constant_stepsize
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ Lf)
    (htraj : is_proximal_gradient_trajectory f.toExtendedReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L) (k : ℕ) :
    ‖G[hLconst.stepsize; f, g] (x (k + 1))‖ ≤ ‖G[hLconst.stepsize; f, g] (x k)‖ := sorry

section

variable {XStar : Set E} {FOpt : ℝ}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f.toExtendedReal g XStar FOpt Lf]

-- Proof sketch: combine clause (1) with the running-minimum rate estimate from Theorem 10.26 in
-- the constant-stepsize regime `α = β = 1`. Because the residual norms are nonincreasing, the
-- current norm `‖G_(L_f)(x^k)‖` agrees with the minimum over the prefix `x^0, ..., x^k`, yielding
-- the displayed `O(1 / k)` bound. The convex-composite problem owner supplies only the optimizer
-- data and the canonical regularity instances for `g`; clause (b) therefore uses the owner-level
-- bridge `hproblem.gradientMapping hLconst.stepsize` instead of theorem-type `letI` plumbing.
/-- Theorem 10.27 (2): clause (b). Under the convex composite problem hypotheses used by
Theorem 10.26 and the same constant stepsize rule, every optimizer `xStar ∈ X^*` gives the
pointwise `O(1 / k)` estimate
`‖G_(L_f)(x^k)‖ ≤ 2 L_f ‖x^0 - xStar‖ / (k + 1)`. -/
theorem proximal_gradient_mapping_norm_le_one_div_k_of_constant_stepsize
    (htraj : is_proximal_gradient_trajectory f.toExtendedReal g x L)
    (hLconst : uses_proximal_gradient_Lf_stepsize_rule Lf L)
    (xStar : E) (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖hproblem.gradientMapping hLconst.stepsize (x k)‖ ≤
      2 * (Lf : ℝ) * ‖x 0 - xStar‖ / (k + 1 : ℝ) := by
  sorry

end

end
