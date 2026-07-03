import Mathlib
import FirstOrderMethodsinOptimization.Chap12.Definition_12_15
import FirstOrderMethodsinOptimization.Chap12.Definition_12_17
import FirstOrderMethodsinOptimization.Chap12.Theorem_12_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 12.19 is `source-facing`: it is the `p = 2` accelerated primal-distance estimate for
ADBPG.

Domain sampling against the surrounding Chapter 12 owners shows the three-layer split:
- `IsDualBlockProximalGradientProblem` together with
  `dual_block_proximal_gradient_dual_objective` and `Λ*(f, ![g₁, g₂])` is the source-facing
  two-block problem layer;
- `composite_model_objective f g₁` is the canonical owner of the reduced primal term, replacing
  the raw pointwise sum `x ↦ f x + g₁ x`;
- `IsFastDualProximalGradientPrimalTrajectory`, recalled in Algorithm 12.16, is the bridge/view
  layer expressing ADBPG as accelerated dual proximal gradient on the reduced problem with primal
  term `composite_model_objective f g₁`; and
- `dual_based_proximal_gradient_lagrange_dual_objective_primal` together with
  `dual_based_proximal_gradient_lagrange_dual_problem_value` is the `core/canonical` reduced dual
  owner used only to invoke Theorem 12.10 internally.

Primitive data for the public theorem are the reduced accelerated trajectory, a two-block optimal
dual point `y* ∈ Λ*(f, ![g₁, g₂])`, and the pointwise primal argmax selections at the current
dual iterates and at the second optimal block `y₂*`. The reduced dual optimum condition is
derived API and should stay behind a bridge theorem rather than on the theorem surface. -/

section

variable (σ : PosReal) (f g1 g2 : E → EReal)

local notation "F" => composite_model_objective f g1
local notation "A" => (LinearMap.id : E →ₗ[ℝ] E)
local notation "L" => dual_based_proximal_gradient_identity_stepsize_parameter σ
local notation "qRed" => dual_based_proximal_gradient_lagrange_dual_objective_primal F g2 A
local notation "qRedOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value F g2 A

namespace IsDualBlockProximalGradientProblem

/-- Under Assumption 12.14 with two blocks, the reduced problem with primal term `f + g₁`,
nonsmooth term `g₂`, and identity map satisfies the Chapter 12.1 owner assumptions. -/
theorem toReducedProblem
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    IsDualBasedProximalGradientProblem F g2 A σ := sorry

end IsDualBlockProximalGradientProblem

-- Proof sketch: optimize the two-block dual objective first over the first block. The resulting
-- one-variable dual problem is exactly the reduced Chapter 12 owner for `F = f + g₁`, so the
-- second component of any block-dual maximizer attains the reduced dual optimum.
/-- If `y* = (y₁*, y₂*)` is optimal for the two-block dual objective, then `y₂*` attains the
reduced Chapter 12 dual problem value for `F = f + g₁`. -/
theorem reduced_dual_eq_problem_value_of_mem_optimal_set
    {yStar : Fin 2 → E} (hyStar : yStar ∈ Λ*(f, ![g1, g2])) :
    qRed (yStar 1) = qRedOpt := sorry

-- Proof sketch: combine the reduced dual optimality of `y₂*` with the Chapter 12 primal argmax
-- characterization at that dual point. Under the reduced standing assumptions, an argmax point at
-- an optimal dual solution is a primal minimizer of `x ↦ F x + g₂ x`.
/-- For a two-block dual optimum `y*`, any reduced primal argmax point at `y₂*` is a minimizer of
the reduced primal objective. -/
theorem isMinOn_of_mem_reduced_argmax_of_mem_optimal_set
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    {yStar : Fin 2 → E} (hyStar : yStar ∈ Λ*(f, ![g1, g2]))
    {xStar : E}
    (hxStar : xStar ∈ dual_proximal_gradient_primal_x_argmax F A (yStar 1)) :
    IsMinOn (composite_model_objective F g2) Set.univ xStar := sorry

-- Proof sketch: first use Assumption 12.14 with `p = 2` to view ADBPG as accelerated dual
-- proximal gradient on the reduced problem with primal term `F = f + g₁`.
-- Then identify the primal map
-- `y ↦ argmax_x {⟪x, y⟫ - f(x) - g₁(x)}` with the gradient of `((f + g₁)∗)`, use the
-- `1 / σ`-Lipschitz continuity of that map, and combine it with the accelerated
-- `O(1 / k^2)` dual rate from Theorem 12.10 after bridging the source-facing two-block optimality
-- condition `y* ∈ Λ*(f, ![g₁, g₂])` to the reduced Chapter 12.4 owner.
/-- Theorem 12.19: under Assumption 12.14 with two blocks, if the reduced accelerated
dual-proximal-gradient trajectory represents the ADBPG iterates and `x^k` is chosen from
`argmax_x {⟪x, y^k⟫ - f(x) - g₁(x)}` for each current dual iterate `y^k`, then for any optimal
two-block dual solution `y* = (y₁*, y₂*) ∈ Λ*(f, ![g₁, g₂])` and any associated reduced primal
argmax point `x* ∈ argmax_x {⟪x, y₂*⟫ - f(x) - g₁(x)}`, every positive iterate satisfies
`‖x^k - x*‖² ≤ 4 ‖y^0 - y₂*‖² / (σ² (k + 1)²)`. -/
theorem accelerated_dual_block_proximal_gradient_primal_sqdist_le
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y0 : E) (u x : ℕ → E) (y w : ℕ → E) (t : ℕ → ℝ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax F A (y k))
    (yStar : Fin 2 → E)
    (hyStar : yStar ∈ Λ*(f, ![g1, g2]))
    (xStar : E)
    (hxStar : xStar ∈ dual_proximal_gradient_primal_x_argmax F A (yStar 1))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * ‖y0 - yStar 1‖ ^ (2 : ℕ) /
        (((σ : ℝ) ^ (2 : ℕ)) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
  have h_reduced : IsDualBasedProximalGradientProblem F g2 A σ :=
    IsDualBlockProximalGradientProblem.toReducedProblem σ f g1 g2 h_problem
  have hx_min : IsMinOn (composite_model_objective F g2) Set.univ xStar :=
    isMinOn_of_mem_reduced_argmax_of_mem_optimal_set σ f g1 g2 h_problem hyStar hxStar
  have hy_red : qRed (yStar 1) = qRedOpt :=
    reduced_dual_eq_problem_value_of_mem_optimal_set f g1 g2 hyStar
  have hx_min' : IsMinOn (composite_model_objective F (g2 ∘ A)) Set.univ xStar := by
    simpa using hx_min
  have hsqdist :=
    fast_dual_proximal_gradient_primal_sqdist_le
      F g2 A σ L h_reduced y0 u x y w t htraj hx xStar hx_min' (yStar 1) hy_red k hk
  change
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * ((σ⁻¹ : PosReal) : ℝ) * ‖y0 - yStar 1‖ ^ (2 : ℕ) /
        ((σ : ℝ) * ((k + 1 : ℝ) ^ (2 : ℕ))) at hsqdist
  simpa [PosReal.coe_inv, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hsqdist

end

end
