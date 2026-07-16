import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Proposition_5_0_15
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_0_21
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Theorem 5.1.8 lies in the Chapter 5 self-concordant Hessian-comparison domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `hessian_loewner_bounds_along_segment` from `Theorem_5_1_7`, the segment-local Hessian
  comparison theorem stated directly in Loewner order;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the bundled-owner Dikin-ellipsoid version of the same owner-level
  comparison.

Source/core/bridge triage:
* source-facing: the gradient-pairing and lower Taylor bounds between two fixed points;
* core/canonical: the Loewner-order comparison on `hessian f _`;
* bridge/view: the scalar local norm `‖y - x‖[f; x]` appearing only in the comparison factor and
  in the final bound.

Primitive data:
* a `C²` function on a set containing the segment from `x` to `y`;
* positivity of the base Hessian `hessian f x`, so the Chapter 5 local norm at `x` is a genuine
  Hessian norm;
* a lower Loewner-order comparison of the Hessian along that segment.

Derived API:
* the lower bound for the gradient pairing;
* the affine lower Taylor bound with remainder `ω`.

This file stays source-facing, but its primitive Hessian hypothesis now uses the owner
`hessian f _` directly instead of the derived scalarized quadratic-form surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
variable (hcont : ContDiffOn ℝ 2 f dom)
variable (hsegment : segment ℝ x y ⊆ dom)
variable (hHessPos : (hessian f x).IsPositive)
variable
  (hloewnerLower :
    ∀ ⦃z : E⦄, z ∈ segment ℝ x y →
      (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) • hessian f x ≤ hessian f z)

include hcont hsegment hHessPos hloewnerLower

-- Proof sketch: integrate the Loewner-order Hessian comparison along the segment
-- `y_τ = x + τ • (y - x)`. The base-point positivity hypothesis makes `‖y - x‖[f; x]` a genuine
-- Hessian norm, and `hloewnerLower` transports that positivity along the segment. The
-- fundamental theorem
-- of calculus gives
-- `∇ f(y) - ∇ f(x) = ∫₀¹ ∇² f(y_τ) (y - x) dτ`, and evaluating `hloewnerLower` on the
-- direction `y - x`
-- yields the scalar lower bound `r² / (1 + τ M_f r)^2` for the integrand, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral gives the stated denominator
-- `1 + M_f r`.
/-- Theorem 5.1.8 (1): if a `C²` function has positive base Hessian `∇² f(x)` and along the
segment from `x` to `y` satisfies the lower Loewner-order Hessian comparison
`∇² f(z) ≽ (1 + M_f ‖z - x‖_x)⁻² ∇² f(x)`, then the gradient increment paired with `y - x`
is bounded below by `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div :
    let r := ‖y - x‖[f; x]
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) := sorry

-- Proof sketch: write
-- `f y - f x - ⟪∇ f(x), y - x⟫ = ∫₀¹ ⟪∇ f(y_τ) - ∇ f(x), y - x⟫ dτ`
-- along the segment `y_τ = x + τ • (y - x)`, then apply clause (1) to each pair `(x, y_τ)`.
-- This gives the integrand lower bound `τ r² / (1 + τ M_f r)`, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral yields
-- `(1 / M_f²) * ω(M_f r)` when `M_f > 0`, and its limiting value `(1 / 2) r²` when `M_f = 0`.
/-- Theorem 5.1.8 (2): under the same owner-level Hessian comparison along the segment from `x`
to `y` and the same base-Hessian positivity hypothesis at `x`, the function value at `y` admits
the affine lower Taylor bound at `x` with remainder
`M_f⁻² ω(M_f ‖y - x‖_x)`, interpreted as `(1 / 2) ‖y - x‖_x²` when `M_f = 0`. -/
theorem taylor_lower_bound_of_hessian_loewner_lower :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := sorry

end

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: derive `y ∈ dom` from the Dikin-step hypothesis via
-- `openDikinEllipsoid_inv_constant_subset`, use convexity of `dom` to place the whole segment
-- from `x` to `y` inside `dom`, and apply
-- `hessian_loewner_bounds_of_mem_openDikinEllipsoid` pointwise to the intermediate points
-- `x + τ • (y - x)` to recover the lower segment-wise Loewner hypothesis required by the
-- source-facing Theorem 5.1.8. The two displayed estimates then follow by the local theorems
-- `gradient_difference_inner_ge_hessianLocalNorm_sq_div` and
-- `taylor_lower_bound_of_hessian_loewner_lower`.
/-- Under the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`, every admissible Dikin step
`y ∈ W⁰[f; x](1 / (Mf : ℝ))` satisfies both lower bounds from Theorem 5.1.8: the gradient pairing
dominates `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`, and the function value dominates the affine Taylor
approximation at `x` with the explicit self-concordant remainder `ω`. This is the canonical
owner-level bridge from self-concordance to the source-facing lower estimates. -/
theorem gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
        r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ∧
      f y ≥
        f x + inner ℝ (∇ f x) (y - x) +
          if hMf : Mf = 0 then
            r ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := sorry

-- Proof sketch: project the first component of the owner-level conjunction above.
/-- The owner-level gradient-pairing lower bound derived from `IsSelfConcordantOnWith dom Mf f`
and the admissible Dikin-step hypothesis. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      ‖y - x‖[f; x] ^ (2 : ℕ) / (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).1

-- Proof sketch: project the second component of the owner-level conjunction above.
/-- The owner-level Taylor lower bound with remainder `ω`, derived from
`IsSelfConcordantOnWith dom Mf f` and the admissible Dikin-step hypothesis. -/
theorem taylor_lower_bound_with_selfConcordantOmega_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).2

end

end IsSelfConcordantOnWith

end
