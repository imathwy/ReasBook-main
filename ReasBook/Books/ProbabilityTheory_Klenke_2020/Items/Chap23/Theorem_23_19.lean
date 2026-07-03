import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]

/-- The tilted rate function from (23.21), namely the nonnegative extended-real gap between the
global supremum of `φ - I` and its value at `x`, viewed as an `ℝ≥0∞`-valued map. -/
def tiltedRateFunction (I : E → ENNReal) (φ : E → ℝ) : E → ENNReal :=
  fun x ↦
    (sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
      (((φ x : EReal) - (I x : EReal)))).toENNReal

-- Proof sketch: unfold `tiltedRateFunction`; the right-hand side is exactly the formula
-- `sup_z (φ z - I z) - (φ x - I x)` from (23.21), interpreted in `EReal` and then converted back
-- to `ℝ≥0∞` via `EReal.toENNReal`.
/-- Unfolding `tiltedRateFunction I φ` gives the shifted supremum formula from (23.21). -/
theorem tiltedRateFunction_def (I : E → ENNReal) (φ : E → ℝ) (x : E) :
    tiltedRateFunction I φ x =
      (sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
        (((φ x : EReal) - (I x : EReal)))).toENNReal := sorry

-- Proof sketch: apply `isProbabilityMeasure_tilted` to the underlying measure of the probability
-- measure `ν`; the integrability hypothesis is already stated in the exact form required by the
-- tilted-measure API.
/-- The tilted measure of a probability measure is again a probability measure when the exponential
weight is integrable. -/
theorem tilted_isProbabilityMeasure_of_probabilityMeasure
    (ν : ProbabilityMeasure E) (f : E → ℝ)
    (hf : Integrable (fun x ↦ Real.exp (f x)) (ν : Measure E)) :
    IsProbabilityMeasure ((ν : Measure E).tilted f) := sorry

/-- The exponentially tilted family `μᵠ_ε(dx) ∝ exp (φ x / ε) μ_ε(dx)` on the positive parameter
space `ε > 0`. -/
def tiltedProbabilityMeasureFamily
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E)) :
    PositiveProbabilityFamily E :=
  fun ε ↦
    ⟨(μ ε : Measure E).tilted (fun x ↦ φ x / (ε : ℝ)),
      tilted_isProbabilityMeasure_of_probabilityMeasure
        (μ ε) (fun x ↦ φ x / (ε : ℝ)) (h_integrable ε)⟩

-- Proof sketch: unfold `tiltedProbabilityMeasureFamily`; the result is exactly the exponentially
-- tilted measure `(μ ε).tilted (fun x ↦ φ x / ε)`.
/-- Evaluating `tiltedProbabilityMeasureFamily μ φ h_integrable` at `ε > 0` gives the textbook's
exponentially tilted law. -/
theorem tiltedProbabilityMeasureFamily_apply
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    (ε : PositiveParameter) :
    (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E) =
      (μ ε : Measure E).tilted (fun x ↦ φ x / (ε : ℝ)) := rfl

-- Proof sketch: apply Varadhan's lemma to the logarithmic normalizing constants of the tilted
-- family, rewrite the logarithmic probabilities of open and closed sets under the tilted laws as
-- the original logarithmic probabilities shifted by the normalizer, and identify the resulting
-- bounds with the rate `tiltedRateFunction I φ`.
/-- Theorem 23.19: if `μ_ε` satisfies an LDP with good rate function `I`, `φ` is continuous and
satisfies the tail condition (23.17), then the exponentially tilted laws
`μ_ε^φ(dx) ∝ exp (φ x / ε) μ_ε(dx)` satisfy an LDP with tilted rate function
`tiltedRateFunction I φ`, i.e. with rate
`x ↦ sup_z (φ z - I z) - (φ x - I x)` from (23.21). -/
theorem hasLargeDeviationsPrinciple_tilted
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hI_good : IsGoodRateFunction I)
    (hLDP : HasLargeDeviationsPrinciple μ I)
    (hφ : Continuous φ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    (h_tail :
      sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict
                {x | M.1 ≤ φ x})))
          positiveParameterFilter) = ⊥) :
    HasLargeDeviationsPrinciple
      (tiltedProbabilityMeasureFamily μ φ h_integrable)
      (tiltedRateFunction I φ) := sorry

end ProbabilityTheory
