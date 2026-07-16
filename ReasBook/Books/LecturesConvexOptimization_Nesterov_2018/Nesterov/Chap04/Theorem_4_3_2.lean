import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Lemma_4_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.3.2 lies in the optimal cubic-Newton estimating-sequence rate domain on a
finite-dimensional real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod` in `Algorithm_4_3_1`, the chapter owner for the iterate sequence,
  the cubic Newton step `T_M`, the estimating functions `ψ_k`, and the accumulated weights `A_k`;
* `OptimalCubicNewtonMethod.psi_isMin` in `Algorithm_4_3_1`, the derived owner theorem recording
  that each `v_k` minimizes `ψ_k`;
* `OptimalCubicNewtonMethod.accumulated_weight_lower_bound` in `Lemma_4_3_5`, the predecessor
  owner theorem producing the lower bound on `A_k` from the residual sandwich and the estimating
  majorization at `xStar`.

Best owner abstraction:
* core/canonical: `OptimalCubicNewtonMethod B Mf f x0 sigma`

Primitive data:
* the method data already stored by `OptimalCubicNewtonMethod`
* the comparison point `xStar`
* the scalar sandwich factor `γ`

Derived API:
* the estimating-function majorization at the comparison point `xStar`
* the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)`
* the lower bound on the accumulated weights `A_k`

Source/core/bridge triage:
* source-facing: Theorem 4.3.2's inverse-`7/2` objective-gap estimate
* core/canonical: the owner `OptimalCubicNewtonMethod`
* bridge/view: the passage from the accumulated-weight lower bound to the explicit rate
-/

section

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 xStar : PrimalSpace B} {sigma γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 sigma)

namespace OptimalCubicNewtonMethod

-- Proof sketch: combine Lemma 4.3.4 with the upper majorization of `ψ_k` at the comparison point
-- `xStar` to get
-- `f (method k) - f xStar ≤ (1 / (2 * method.A k)) * ‖x₀ - xStar‖^2` for `k ≥ 1`. Then apply
-- `method.accumulated_weight_lower_bound` to bound `method.A k` from below and simplify the
-- resulting reciprocal estimate using `M = M_f / σ`.
/-- Theorem 4.3.2: if `f` is convex, the auxiliary parameters of Algorithm 4.3.1 satisfy
the residual sandwich `r_M(y_k) ≤ ρ_k ≤ γ r_M(y_k)` from Lemma 4.3.5, and the estimating
functions are majorized at a comparison point `xStar` by
`A_k f(xStar) + (1 / 2) ‖x₀ - xStar‖^2`, then Algorithm 4.3.1 with `M = M_f / σ` satisfies, for
every `k ≥ 1`,
`f(x_k) - f(xStar) ≤ (2 γ^(3/2) M_f ‖x₀ - xStar‖^3 / (σ * √(1 - σ^2))) * (3 / (2k + 1))^(7/2)`,
where the norm is the primal norm induced by `B`. -/
theorem gap_le_inverse_seven_halves_rate
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hpsi_upper : ∀ k : ℕ,
      let Δ := x0 - xStar
      method.psi k xStar ≤
        method.A k * f xStar + (1 / 2 : ℝ) * ‖Δ‖[B] ^ (2 : ℕ))
    (hresidual_lower : ∀ k : ℕ, r[(method.step)] (method.y k) ≤ method.rho k)
    (hresidual_upper : ∀ k : ℕ, method.rho k ≤ γ * r[(method.step)] (method.y k))
    {k : ℕ} (hk : 1 ≤ k) :
    let Δ := x0 - xStar
    f (method k) - f xStar ≤
      (((2 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
          ‖Δ‖[B] ^ (3 : ℕ) /
        (sigma * Real.sqrt (1 - sigma ^ (2 : ℕ)))) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := sorry

end OptimalCubicNewtonMethod

end
