import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Algorithm_4_3_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.4 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_zero` in `Algorithm_4_3_1`
* `OptimalCubicNewtonMethod.psi_succ` in `Algorithm_4_3_1`
* `CubicNewtonStep.residual` in `Definition_4_3_6`
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`

Derived API:
* the estimating functions `ψ_k`
* the cubic-step residuals `r[(method.step)] (method.y k)`
* the accumulated lower-bound correction term `B_k`
* the convex lower-support inequality from `ConvexOn.lower_tangent_plane`

Source/core/bridge triage:
* source-facing: Lemma 4.3.4's lower bound
  `A_k f(x_k) + B_k ≤ ψ_k(v_k)`
* core/canonical: the owner `OptimalCubicNewtonMethod` with its `psi` recursion
* bridge/view: the scalar correction term `B_k`, derived from the method data rather than stored
  as extra primitive structure
-/

namespace OptimalCubicNewtonMethod

/-- The accumulated cubic correction term `B_k` from the estimating-sequence lower bound. -/
def estimatingLowerBoundCorrection
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    ℕ → ℝ :=
  fun k ↦
    (((1 - sigma ^ (2 : ℕ)) / 4 : ℝ) * ((Mf : ℝ) / sigma)) *
      Finset.sum (Finset.range k) fun i ↦
        method.A (i + 1) * (r[(method.step)] (method.y i)) ^ (3 : ℕ)

/-- The cubic correction term vanishes at the initial stage `k = 0`. -/
@[simp] theorem estimatingLowerBoundCorrection_zero
    {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
    [Fact B.toQuadraticMap.PosDef]
    {x0 : PrimalSpace B} {sigma : ℝ}
    (method : OptimalCubicNewtonMethod B Mf f x0 sigma) :
    method.estimatingLowerBoundCorrection 0 = 0 := by
  sorry

end OptimalCubicNewtonMethod

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma)

/-- Lemma 4.3.4: if `f` is convex and the algorithmic parameters satisfy
`r_M(y_k) ≤ ρ_k` for every `k`, then `A_k f(x_k) + B_k` is bounded above by
`ψ_k(v_k) = ψ_k^* = min_x ψ_k(x)`, where `B_k` is the accumulated cubic correction term
`((1 - σ^2) / 4) M * ∑_{i=0}^{k-1} A_{i+1} r_M(y_i)^3`. -/
-- Proof sketch: argue by induction on `k`. Use the recursion for `ψ_{k+1}`, the convexity bound
-- comparing `f(x_k)` and the linearization at `x_{k+1}`, minimize the resulting quadratic term at
-- `v_k`, apply `cubicNewtonStep_dualPairing_lower_bound_of_sigma` at `y_k`, and absorb the new
-- cubic contribution into the recursive definition of the correction term.
lemma optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hresidual : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (k : ℕ) :
    method.A k * f (method k) +
        method.estimatingLowerBoundCorrection k ≤
      method.psi k (method.v k) := sorry

end
