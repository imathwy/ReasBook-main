import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Remark 10.20 is `bridge/view` in the Chapter 10 proximal-gradient API.

Domain sampling in the proximal-gradient layer identifies:
- `is_proximal_gradient_trajectory` from Algorithm 10.1 as the source-facing owner for the
  iterate sequence `x^k`;
- `mem_proximal_gradient_step_iff_isMinOn_curvature_model` from Algorithm 10.66 as the canonical
  curvature-model bridge for one proximal-gradient step in the complete inner-product setting;
- `composite_model_objective` from Definition 10.2 as the chapter owner for the composite value
  `F = f + g`;
- the stronger `ProperSpace`/single-valued bridge
  `prox_grad_sufficient_decrease_of_upper_model` as the packaged descendant of the same
  upper-model mechanism once `g` is upgraded to the prox-gradient operator setting.

Primitive data here are therefore just:
- a proximal-gradient trajectory `x`;
- the explicit upper-model inequality at the realized successor iterate `x^(k+1)`.

The descent inequality and the monotonicity consequence are derived API from that source-facing
data, so this file keeps the weaker trajectory-level formulation as the main entry rather than
strengthening it to the single-valued B2 owner. In particular, the owner
`is_proximal_gradient_trajectory` already lives over `[CompleteSpace E]`, so finite-dimensionality
would be non-primitive ambient data here and is intentionally not part of the public API. -/

section

variable {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: use `is_proximal_gradient_trajectory_step` together with the canonical
-- curvature-model bridge from Algorithm 10.66 to view `x (k + 1)` as a minimizer of the one-step
-- quadratic model at `x k`. Testing that minimizing property against `x k` gives the inequality
-- for the nonsmooth term plus the quadratic penalty. Adding the assumed local upper-model bound
-- for `f (x (k + 1))` and rewriting with `composite_model_objective` yields the displayed descent
-- estimate.
/-- Remark 10.20: if `x` is a proximal-gradient trajectory for `f + g` and the local quadratic
upper model of `f` at iteration `k` holds with curvature parameter `L k`, then the composite
objective satisfies the one-step descent inequality
`F(x^(k+1)) + (L_k / 2) ‖x^(k+1) - x^k‖² ≤ F(x^k)`, where `F = f + g`. -/
theorem proximal_gradient_descent_ineq_of_upper_model
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ)
    (hmodel :
      f (x (k + 1)) ≤
        (((f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal)) :
    F (x (k + 1)) +
        ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) ≤
      F (x k) := by
  -- TODO: the current hypotheses yield the standard model-comparison inequality
  -- `g (x (k + 1)) + <∇f(x^k), x^(k+1) - x^k> + (L_k / 2) ‖x^(k+1) - x^k‖² ≤ g (x^k)`,
  -- which combines with `hmodel` to prove monotonicity `F (x (k + 1)) ≤ F (x k)`. The stronger
  -- displayed descent bound with an extra quadratic term requires additional convex/optimality
  -- input that is not present in this declaration.
  sorry

end

section

variable {E : Type u} [NormedAddCommGroup E]
variable {f g : E → EReal} {x : ℕ → E} {L : ℕ → PosReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: the correction term in the descent inequality is nonnegative because `L k > 0`
-- by definition of `PosReal` and squared norms are nonnegative. Dropping this term gives the
-- monotonicity of the composite objective values.
/-- Helper for Remark 10.20: the quadratic correction term appearing in the descent estimate is
always nonnegative. -/
lemma proximal_gradient_quadratic_term_nonneg (k : ℕ) :
    0 ≤ ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) := by
  -- Positivity of the stepsize and of squared norms gives positivity of the real coefficient.
  have hL_half_nonneg : 0 ≤ (L k : ℝ) / 2 := by
    have hL_pos : 0 < (L k : ℝ) := PosReal.coe_pos (L k)
    linarith
  have hsq_nonneg : 0 ≤ ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
    exact sq_nonneg ‖x (k + 1) - x k‖
  exact_mod_cast mul_nonneg hL_half_nonneg hsq_nonneg

/-- A quadratic descent bound for one proximal-gradient step implies monotonicity of the composite
objective at that step. -/
theorem composite_model_objective_monotone_of_descent_ineq
    {k : ℕ}
    (hdescent :
      F (x (k + 1)) +
          ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) ≤
        F (x k)) :
    F (x (k + 1)) ≤ F (x k) := by
  -- First insert the nonnegative correction term on the left-hand side.
  have hleft :
      F (x (k + 1)) ≤
        F (x (k + 1)) +
          ((((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) := by
    exact le_add_of_nonneg_right (proximal_gradient_quadratic_term_nonneg (x := x) (L := L) k)
  -- Then compose with the assumed descent estimate.
  exact le_trans hleft hdescent

end

end
