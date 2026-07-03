import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

noncomputable section

/-- The Gaussian family `μ_ε = 𝒩(0, ε²)` from Exercise 23.2.2. -/
def smallVarianceGaussianFamily : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ⟨gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩, inferInstance⟩

-- Proof sketch: unfold `smallVarianceGaussianFamily`; the statement is exactly its defining
-- equation.
/-- Evaluating `smallVarianceGaussianFamily` at `ε` gives the centered Gaussian law with variance
`ε²`. -/
theorem smallVarianceGaussianFamily_apply (ε : PositiveParameter) :
    (smallVarianceGaussianFamily ε : Measure ℝ) =
      gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩ := sorry

/-- The rate function from Exercise 23.2.2, equal to `0` at the origin and `∞` away from `0`. -/
def zeroDiracRateFunction (x : ℝ) : ℝ≥0∞ :=
  if x = 0 then 0 else ⊤

-- Proof sketch: unfold `zeroDiracRateFunction`; when `x ≠ 0` the defining `if` takes the second
-- branch.
/-- Away from the origin, `zeroDiracRateFunction` is infinite. -/
theorem zeroDiracRateFunction_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    zeroDiracRateFunction x = ⊤ := sorry

-- Proof sketch: the Gaussian family collapses exponentially fast onto the singleton `{0}` as
-- `ε ↓ 0`, so the large-deviation bounds are governed by the rate that is `0` at `0` and `∞`
-- elsewhere; the finite sublevel sets are either empty or `{0}`, hence compact.
/-- Exercise 23.2.2: the family `μ_ε = 𝒩(0, ε²)` satisfies the large deviations principle with
good rate function `I(x) = ∞ · 𝟙_{ℝ \ {0}}(x)`, written here as the function that is `0` at `0`
and `∞` elsewhere. -/
theorem smallVarianceGaussianFamily_satisfiesLDPWithGoodRate :
    HasLargeDeviationsPrinciple smallVarianceGaussianFamily zeroDiracRateFunction ∧
      IsGoodRateFunction zeroDiracRateFunction := sorry

-- Proof sketch: take the open set `(0, ∞)`. Its rate infimum is `∞`, so the LDP lower bound gives
-- only `-∞`, while the Gaussian symmetry gives `μ_ε (0, ∞) = 1 / 2`, hence `ε log μ_ε (0, ∞) → 0`.
/-- The open half-line `(0, ∞)` witnesses that the lower bound in the large deviations principle
can be strict for `μ_ε = 𝒩(0, ε²)`. -/
theorem smallVarianceGaussianFamily_strict_lowerBound_on_positiveHalfline :
    -sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' Set.Ioi (0 : ℝ)) <
      liminf
        (scaledLogMassAlong (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) (fun ε ↦ ε)
          (Set.Ioi (0 : ℝ)))
        positiveParameterFilter := sorry
