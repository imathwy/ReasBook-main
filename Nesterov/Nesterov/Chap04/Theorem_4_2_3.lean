import Nesterov.Chap04.Algorithm_4_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 4.2.3 lies in the chapter accelerated cubic-Newton / estimating-sequence domain.

Sampled owner declarations:
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `f ∈ C22[L3]`, in
  `Definition_4_2_7`, the chapter owner for `C²` regularity plus global Hessian-Lipschitz
  control;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for the iterate
  sequence, estimating-function minimizers, accumulated weights, and the standing
  `C22[L3]` smoothness hypothesis;
* `AcceleratedCubicNewtonMethod.psi`, `psi_one`, and `psi_succ` in `Algorithm_4_2_2`, the
  canonical derived estimating-function surface replacing a primitive family `ψ_k`;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized at each accelerated step.

Best owner abstraction:
* source-facing: the inverse-cubic objective-gap estimate for an accelerated cubic Newton method;
* core/canonical: `AcceleratedCubicNewtonMethod`, `cubicRegularizationQuadraticApproximation`,
  and `f ∈ C22[L3]`;
* bridge/view: the owner theorems `method.x_one_isMinOn` and `method.x_succ_isMinOn` recovering
  the textbook minimizing facts for the actual cubic steps used by the algorithm.

Primitive data:
* the objective `f`;
* the accelerated method owner `method`;
* convexity of `f`;
* a global minimizer `xStar`.

Derived API:
* `ContDiff ℝ 2 f` and global `L₃`-Lipschitz control of `hessian f`, both supplied by
  `method.objective_mem`;
* the iterate sequence `x_k`, minimizing sequence `v_k`, estimating functions `ψ_k`, and weights
  `A_k`;
* the initialization `x₁ = T_{L₃}(x₀)`;
* the recursive interpolation and estimating-function update formulas.

The previous statement stored `x`, `v`, `psi`, and `A` as primitive theorem inputs even though
Chapter 4 already owns exactly that data in `AcceleratedCubicNewtonMethod`. This refinement moves
the public surface to that owner, keeps the chapter smoothness hypothesis on the owner itself
instead of splitting it off as a parallel theorem argument, makes the iterate index explicit, and
derives the two actual model-minimization facts from the method's cubic-step owner instead of
keeping them as redundant external assumptions.
-/

-- Proof sketch: prove by induction on `k` the estimating-sequence relations
-- `method.A k * f (method k) ≤ sInf (Set.range (method.psi k))` and
-- `method.psi k z ≤ method.A k * f z + (4 / 3) * L₃ * ‖z - x₀‖^3`.
-- The base step uses the initialization `method 1 = T_{L₃}(x₀)`, `method.psi_one`, and
-- `method.x_one_isMinOn`.
-- For the inductive step, combine convexity of `f`, the minimizing property of `method.v k`, the
-- recursion for `method (k + 1)` and `method.psi (k + 1)`, and the fact that the two actual
-- cubic models used by the algorithm are globally minimized at the chosen iterates via
-- `method.x_succ_isMinOn hk`. Evaluating
-- the upper bound at `xStar`, using `method.A k = k (k + 1) (k + 2) / 6`, and rearranging gives
-- the stated
-- `O(1 / k^3)` estimate.
/-- Theorem 4.2.3: let `method` be the accelerated cubic Newton method. If `f ∈ C22[L3]` is
convex, then every iterate with index `k ≥ 1` satisfies
`f(x_k) - f(x^*) ≤ 8 L₃ ‖x₀ - x^*‖^3 / (k (k + 1) (k + 2))`. -/
theorem acceleratedCubicRegularization_gap_le_inverse_cubic_rate
    {f : E → ℝ} {L3 : NNReal} {x0 xStar : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) (hk : 1 ≤ k) :
      f (method k) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  sorry
