import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerConeGeometricMean

/- Theorem 5.4.7.2 lies in the Chapter 5 power-cone compatibility domain.

Sampled owner declarations:
* `powerConeGeometricMean`, `powerConeQ1`, and `powerConeBarrier` from `Definition_5_4_7_1`, the
  earlier source-facing power-cone data on raw pairs;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for compatibility;
* `Chap05RealProdL2.instInnerProductSpaceRealProd` from `RealProdL2`, the chapter owner bridge
  equipping the raw pair model `ℝ × ℝ` with the canonical Euclidean `L²` ambient structure;
* `entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier` from
  `Theorem_5_4_7_6`, the nearby compatibility theorem on the same raw-pair orthant owner.

Source/core/bridge triage:
* source-facing: the `β = 1` compatibility theorem for the weighted geometric mean on `Q₁`;
* core/canonical: `IsBetaCompatibleWith` together with the raw-pair owners from
  `Definition_5_4_7_1`;
* bridge/view: the chapter `RealProdL2` owner activation that realizes the raw pair ambient
  structure through the canonical `L²` model.

Primitive data:
* the orthant `powerConeQ1`;
* the orthant barrier `powerConeBarrier`;
* the scalar cone `ConvexCone.positive ℝ ℝ`;
* the weighted geometric mean `ξ[α]`.

Derived API:
* the `β = 1` compatibility theorem below.

This file therefore reuses the raw-pair owners directly and keeps no parallel `WithLp` pullback
copy of the same compatibility statement. -/

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

-- Proof sketch: use the explicit formula for `D³ξ(x)[h,h,h]` in terms of `-D²ξ(x)[h,h]`, and
-- compute `hessianLocalNorm powerConeBarrier x h` as
-- `((h.1 / x.1)^2 + (h.2 / x.2)^2)^(1/2)` on the positive orthant. Cauchy--Schwarz then bounds
-- the linear factor `((2 - α) (h.1 / x.1) + (1 + α) (h.2 / x.2))` by
-- `3 * hessianLocalNorm powerConeBarrier x h` when `0 < α < 1`, yielding the defining cone-order
-- inequality in the positive cone of `ℝ`.
/-- Theorem 5.4.7.2: for `0 < α < 1`, the weighted geometric mean
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` is `1`-compatible with the logarithmic barrier
`F(x) = -log x^(1) - log x^(2)` on the orthant `Q₁ = ℝ_+²`, relative to the scalar cone
`ℝ_+`. -/
theorem powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ[α] := by
  sorry
