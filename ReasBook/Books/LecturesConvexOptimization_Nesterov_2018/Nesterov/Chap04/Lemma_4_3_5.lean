import LecturesConvexOptimization_Nesterov_2018.Chap04.Lemma_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.5 lies in the optimal cubic-Newton estimating-sequence domain on a finite-dimensional
real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.psi` in `Algorithm_4_3_1`, the owner evaluation of the estimating
  sequence `ψ_k`;
* `OptimalCubicNewtonMethod.estimatingLowerBoundCorrection` in `Lemma_4_3_4`, the derived
  correction term `B_k` attached to a method;
* `optimalCubicNewtonMethod_accumulated_value_le_estimating_minimum` in `Lemma_4_3_4`, the
  predecessor lemma bounding `A_k f(x_k) + B_k` by `ψ_k(v_k)`;
* `CubicNewtonStep.residual` in `Definition_4_3_6`, the owner residual `r_M`.

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`
* the comparison point `xStar`
* the scalar sandwich factor `γ`

Derived API:
* the majorization of `ψ_k` at `xStar`
* the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)`
* the lower bound on the accumulated weights `A_k`

Source/core/bridge triage:
* source-facing: Lemma 4.3.5's quantitative lower bound on the accumulated weights `A_k`
* core/canonical: the owner `OptimalCubicNewtonMethod` and its derived correction term from
  Lemma 4.3.4
* bridge/view: the passage from the residual sandwich to a bound on the scalar recursion for
  `A_k`
-/

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 : PrimalSpace B} {sigma γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma) {xStar : PrimalSpace B}

namespace OptimalCubicNewtonMethod

-- Proof sketch: combine Lemma 4.3.4 with the upper majorization of the estimating sequence at the
-- comparison point `xStar` to get the uniform correction bound
-- `method.estimatingLowerBoundCorrection k ≤ (1 / 2) ‖x₀ - xStar‖²`. Then use
-- the residual sandwich `r_M(y_i) ≤ ρ_i ≤ γ r_M(y_i)` to convert the correction bound into a
-- lower bound on `∑ i < k, ρ_i⁻¹ᐟ²`, optimize that sum under the correction constraint as in the
-- textbook Lagrange-multiplier argument, and finally bootstrap the resulting recursion in `A_k`.
/-- Lemma 4.3.5: if `f` is convex, `γ ≥ 1`, the auxiliary parameters of Algorithm 4.3.1 satisfy
`r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)` for every `k`, and the estimating functions are majorized at the
comparison point `xStar` by `A_k f(xStar) + (1 / 2) ‖x₀ - xStar‖²`, then every index `k ≥ 1`
satisfies the denominator-free accumulated-weight lower bound
`(1 / 4) (1 / γ)^(3/2) * sqrt (1 - σ^2) * ((2k + 1) / 3)^(7/2) ≤ M ‖x₀ - xStar‖ A_k`,
with `M = M_f / σ` and the norm induced by `B`. This is the textbook lower bound on `A_k`,
rewritten to avoid the degenerate totalized division artifact when `x₀ = xStar`. -/
theorem accumulated_weight_lower_bound
    (hγ : 1 ≤ γ)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    let M : ℝ := (Mf : ℝ) / sigma
    ((1 / 4 : ℝ) * Real.rpow (1 / γ) (3 / 2 : ℝ) * Real.sqrt (1 - sigma ^ (2 : ℕ))) *
        Real.rpow ((2 * k + 1 : ℝ) / 3) (7 / 2 : ℝ) ≤
      M * ‖Δ‖[B] * method.A k := sorry

end OptimalCubicNewtonMethod

end
