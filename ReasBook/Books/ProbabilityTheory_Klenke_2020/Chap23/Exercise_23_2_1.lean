import Mathlib
import ProbabilityTheory_Klenke_2020.Chap23.Definition_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

/-- The quadratic rate function `x ↦ x^2 / 2` valued in `ℝ≥0∞`. -/
noncomputable def gaussianQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (x ^ 2 / 2)

/-- The same quadratic rate function viewed in `EReal` for the variational bounds. -/
noncomputable def gaussianQuadraticRateFunctionEReal (x : ℝ) : EReal :=
  gaussianQuadraticRateFunction x

/-- The small-variance centered Gaussian law `μ_ε = N(0, ε)` for positive `ε`. -/
noncomputable def centeredGaussianSmallVarianceLaw (ε : ℝ) : Measure ℝ :=
  gaussianReal 0 (Real.toNNReal ε)

/-- The exponential rate expression `ε log μ_ε(s)` used in the LDP bounds. -/
noncomputable def centeredGaussianSmallVarianceExponent (s : Set ℝ) (ε : ℝ) : EReal :=
  (ε : EReal) * ENNReal.log (centeredGaussianSmallVarianceLaw ε s)

-- Proof sketch: the map `x ↦ x ^ 2 / 2` is continuous on `ℝ`, hence lower semicontinuous after
-- composing with `ENNReal.ofReal`; its finite sublevel sets are closed bounded intervals, so they
-- are compact by Heine--Borel.
/-- Exercise 23.2.1 (1): the quadratic map `I(x) = x^2 / 2`, viewed as an `ℝ≥0∞`-valued map, is a
good rate function on `ℝ`: it is lower semicontinuous and every finite sublevel set is compact. -/
theorem gaussianQuadraticRateFunction_isGood :
    IsGoodRateFunction gaussianQuadraticRateFunction := sorry

-- Proof sketch: evaluate the Gaussian cumulant generating function, derive the exponential lower
-- bound by the standard Laplace-Varadhan argument, and identify the Legendre transform with
-- `x ↦ x^2 / 2` as `ε ↓ 0`.
/-- Exercise 23.2.1 (2): for every open set `G ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP lower bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_lowerBound :
    ∀ G : Set ℝ, IsOpen G →
      -sInf (gaussianQuadraticRateFunctionEReal '' G) ≤
        Filter.liminf (centeredGaussianSmallVarianceExponent G) (𝓝[>] (0 : ℝ)) := sorry

-- Proof sketch: apply Gaussian tail estimates or exponential Chebyshev bounds on closed sets,
-- optimize the exponent, and obtain the negative infimum of the quadratic rate function.
/-- Exercise 23.2.1 (3): for every closed set `F ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP upper bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_upperBound :
    ∀ F : Set ℝ, IsClosed F →
      Filter.limsup (centeredGaussianSmallVarianceExponent F) (𝓝[>] (0 : ℝ)) ≤
        -sInf (gaussianQuadraticRateFunctionEReal '' F) := sorry

-- Proof sketch: choose the closed set `{0}`. Since every nondegenerate Gaussian `N(0, ε)` is
-- atomless, `μ_ε({0}) = 0` for all `ε > 0`, so the left-hand side is `-∞`, while the rate side is
-- `-I(0) = 0`.
/-- Exercise 23.2.1 (4): the closed set `{0}` gives a strict instance of the LDP upper bound for
`μ_ε = N(0, ε)`, so equality need not hold in (LDP 2). -/
theorem centeredGaussianSmallVariance_ldp_upperBound_strictAtSingletonZero :
    Filter.limsup (centeredGaussianSmallVarianceExponent ({0} : Set ℝ)) (𝓝[>] (0 : ℝ)) <
      -sInf (gaussianQuadraticRateFunctionEReal '' ({0} : Set ℝ)) := sorry

end ProbabilityTheory
