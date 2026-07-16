import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Theorem_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.3.4 lies in the optimal cubic-Newton rate / scalar prefactor optimization
domain on a finite-dimensional real inner-product space.

Sampled owner-style declarations:
* `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` in `Theorem_4_3_2`, the chapter
  owner of the inverse-`7/2` objective-gap rate for general `σ ∈ (0, 1)`;
* `OptimalCubicNewtonMethod.accumulated_weight_lower_bound` in `Lemma_4_3_5`, the predecessor
  owner theorem underlying that rate;
* mathlib `IsMinOn`, the canonical owner for the scalar minimization statement on `Set.Ioo 0 1`.

Best owner abstractions:
* core/canonical for the algorithmic estimate: `OptimalCubicNewtonMethod B Mf f x0 sigma`
* core/canonical for the scalar optimization: `IsMinOn`

Primitive data:
* the method data already bundled by `OptimalCubicNewtonMethod`
* the comparison point `xStar` and the residual factor `γ`
* the scalar prefactor `σ ↦ 2 / (σ * sqrt (1 - σ^2))`

Derived API:
* the scalar minimization at `σ = 1 / √2`
* the sharp specialization of the general rate theorem at that parameter value

Source/core/bridge triage:
* source-facing: Proposition 4.3.4's optimal-`σ` claim and the resulting sharp inverse-`7/2` rate
* core/canonical: `OptimalCubicNewtonMethod.gap_le_inverse_seven_halves_rate` and `IsMinOn`
* bridge/view: specialize the owner rate theorem to `σ = 1 / √2` and simplify the coefficient
-/

section

/-- Proposition 4.3.4, scalar part: the prefactor in Theorem 4.3.2 is minimized on `(0, 1)` at
`σ = 1 / √2`. -/
theorem inverse_seven_halves_prefactor_isMinOn :
    IsMinOn
      (fun σ : ℝ ↦
        (2 : ℝ) / (σ * Real.sqrt (1 - σ ^ (2 : ℕ))))
      (Set.Ioo (0 : ℝ) 1)
      ((1 : ℝ) / Real.sqrt 2) := sorry

variable {B : BilinForm ℝ E} {Mf : NNRealˣ} {f : PrimalSpace B → ℝ}
  [Fact B.toQuadraticMap.PosDef]
  {x0 xStar : PrimalSpace B} {γ : ℝ}
  (method : OptimalCubicNewtonMethod B Mf f x0 ((1 : ℝ) / Real.sqrt 2))

namespace OptimalCubicNewtonMethod

-- Proof sketch: the prefactor in Theorem 4.3.2 is the scalar function
-- `σ ↦ 2 / (σ * sqrt (1 - σ^2))` on `(0, 1)`. Differentiate this elementary function or,
-- equivalently, maximize `σ * sqrt (1 - σ^2)` on `(0, 1)` to obtain the optimizer
-- `σ = 1 / sqrt 2`. Then specialize
-- `method.gap_le_inverse_seven_halves_rate` to this value of `σ` and simplify
-- the coefficient
-- `2 / ((1 / sqrt 2) * sqrt (1 - (1 / sqrt 2)^2)) = 4`.
/-- Proposition 4.3.4, rate part: under the convexity assumptions of Theorem 4.3.2, the
right-hand-side
coefficient there is minimized at `σ = 1 / √2`; for an optimal cubic Newton method built with
this parameter, one obtains the sharp specialization
`f(x_k) - f(x^*) ≤ 4 γ^{3/2} M_f ‖x₀ - x^*‖^3 (3 / (2k + 1))^{3.5}` for every `k ≥ 1`. -/
theorem gap_le_inverse_seven_halves_rate_best_sigma
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
      (((4 : ℝ) * Real.rpow γ (3 / 2 : ℝ) * (Mf : ℝ)) *
          ‖Δ‖[B] ^ (3 : ℕ)) *
        Real.rpow ((3 : ℝ) / (2 * k + 1 : ℝ)) (7 / 2 : ℝ) := sorry

end OptimalCubicNewtonMethod

end
