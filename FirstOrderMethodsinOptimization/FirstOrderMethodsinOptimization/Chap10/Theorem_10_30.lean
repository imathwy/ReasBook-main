import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Theorem_10_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {σ : PosReal} {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

/- Theorem 10.30 is `source-facing` in the strongly-convex proximal-gradient complexity layer.

Domain sampling in the existing Chapter 10 API identifies:
- `IsCompositeSmoothMinimizationProblem` as the owner of Assumption 10.1;
- `is_proximal_gradient_trajectory` as the owner of the iterate sequence `x^k`;
- `hproblem.SublinearRateStepsizeRule x L htraj α` from Remark 10.19 as the chapter owner of the
  admissible constant/B2 stepsize regime together with its rate factor `α`;
- `proximal_gradient_strongly_convex_objective_gap_le` from Theorem 10.29 as the canonical
  geometric objective-gap estimate already attached to that owner stack.

This file is therefore a direct logarithmic-iteration corollary of that upstream theorem, not a
place for a parallel rate package or a second condition-number API. Primitive data are only the
strong-convexity hypothesis, the proximal-gradient trajectory, the chapter stepsize rule, the
optimizer `xStar`, and the radius bound `R`; the logarithmic complexity estimate is derived API.
The theorem surface should therefore reuse the existing objective owner `F = f + g` and the
chapter notation `κ(Lf, σ)` rather than spelling those notions through longer local expansions. -/

local notation "F" => composite_model_objective f g
local notation "κ" => κ(Lf, σ)

-- Proof sketch: apply `proximal_gradient_strongly_convex_objective_gap_le` from Theorem 10.29 to
-- the index `k - 1`, use positivity of `k : ℕ+` to rewrite `k = (k - 1) + 1`, bound
-- `‖x 0 - xStar‖²` by `R²` via `hR`, and then use the logarithmic lower bound on `k` together with
-- `log (1 - t) ≤ -t` for `t = 1 / (α * κ(Lf, σ))` to dominate the geometric factor by `ε`.
/-- Theorem 10.30: in the strongly convex proximal-gradient setting of Theorem 10.29, if
the positive iteration index `k` satisfies the logarithmic iteration bound
`α κ log (1 / ε) + α κ log (α L_f R^2 / 2) ≤ k`, where `κ = L_f / σ` and `R` bounds
`‖x^0 - x*‖`, then the `k`-th iterate satisfies `F(x^k) - F_opt ≤ ε`. -/
theorem proximal_gradient_strongly_convex_objective_gap_le_of_log_iteration_bound
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (ε : PosReal) (R : ℝ) (hR : ‖x 0 - xStar‖ ≤ R)
    (k : ℕ+)
    (hiter :
      α * κ * Real.log (1 / (ε : ℝ)) +
          α * κ * Real.log (α * (Lf : ℝ) * R ^ (2 : ℕ) / 2) ≤
        (k : ℝ)) :
    F (x k) - (FOpt : EReal) ≤ ((ε : ℝ) : EReal) := sorry

end
