import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Algorithm_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- Algorithm 12.4 is `source-facing` in the chapter's accelerated dual proximal-gradient API.

Domain sampling against the nearby project owners points to:
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the canonical owner for the
  primal argmax step `u^k`;
- `dual_proximal_gradient_primal_y_step` from Algorithm 12.2 as the canonical owner for the
  primal-representation proximal update `y^(k+1)`;
- `fista_momentum_update` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`;
- `DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ` from
  Algorithm 12.1 as the canonical owner of the admissible constant parameter `L`.

The new content of Algorithm 12.4 is the accelerated auxiliary sequences `w^k` and `t_k`.
Because step (d) in the source references `t_{k-1}`, the Lean surface records the first
extrapolated point `w^1 = y^1` separately and then states the momentum recursion in the shifted,
well-typed form for `w^(k+2)`. -/

/-- Algorithm 12.4: a quadruple of sequences `(u^k, y^k, w^k, t_k)` follows the fast dual
proximal-gradient method in primal representation when `L` is an admissible constant stepsize
parameter, equivalently `(L : ℝ) ≥ ‖A‖² / σ`, the initial conditions are `w^0 = y^0 = y0` and
`t_0 = 1`, each `u^k` maximizes
`u ↦ ⟪u, Aᵀ w^k⟫ - f(u)`, each `y^(k+1)` is obtained from the primal proximal step at `w^k`,
the scalar sequence satisfies `t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`, and the momentum update
is recorded as `w^1 = y^1` together with the shifted recursion
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
class IsFastDualProximalGradientPrimalTrajectory
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (u : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ) : Prop where
  /-- The initial dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- The acceleration parameter is initialized by `t_0 = 1`. -/
  t_zero : t 0 = 1
  /-- At each step, `u^k` is a maximizer of `u ↦ ⟪u, Aᵀ w^k⟫ - f(u)`. -/
  primal_step (k : ℕ) :
    u k ∈ dual_proximal_gradient_primal_x_argmax f A (w k)
  /-- At each step, `y^(k+1)` lies in the Chapter 12 primal proximal update set based at `w^k`. -/
  dual_step (k : ℕ) :
    y (k + 1) ∈ dual_proximal_gradient_primal_y_step g A (u k) (w k) L
  /-- The acceleration scalars satisfy the Chapter 10 FISTA momentum recursion. -/
  acceleration_step (k : ℕ) :
    t (k + 1) = fista_momentum_update (t k)
  /-- The first extrapolated iterate is recorded explicitly as `w^1 = y^1`. -/
  first_momentum_step : w 1 = y 1
  /-- For every `k`, the later extrapolated iterates satisfy the shifted textbook momentum
  recursion. -/
  momentum_step (k : ℕ) :
    w (k + 2) =
      y (k + 2) + (t k / t (k + 2)) • (y (k + 2) - y (k + 1))

variable {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V} {σ : PosReal}
variable {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
variable {y0 : V} {u : ℕ → E} {y w : ℕ → V} {t : ℕ → ℝ}

/-- The acceleration field of a fast dual proximal-gradient primal trajectory expands to the
textbook scalar formula
`t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`. -/
theorem IsFastDualProximalGradientPrimalTrajectory.acceleration_step_formula
    (h : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  simpa [fista_momentum_update_eq] using h.acceleration_step k

end
