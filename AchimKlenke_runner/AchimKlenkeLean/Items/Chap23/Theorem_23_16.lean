import Mathlib
import AchimKlenkeLean.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {F : Type v}
variable [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
variable [MeasurableSpace F] [PseudoMetricSpace F] [BorelSpace F]

/-- The rate function obtained by contracting `I` along `m`, defined by taking the infimum of `I`
on each fiber of `m`. -/
def contractedRateFunction (m : E → F) (I : E → ENNReal) : F → ENNReal :=
  fun y ↦ sInf (I '' (m ⁻¹' {y}))

-- Proof sketch: unfold `contractedRateFunction`; the right-hand side is exactly the infimum of
-- `I` over the singleton fiber `m ⁻¹' {y}`.
/-- Expanding `contractedRateFunction m I` gives the infimum of `I` over the fiber of `m` above
`y`. -/
theorem contractedRateFunction_def (m : E → F) (I : E → ENNReal) (y : F) :
    contractedRateFunction m I y = sInf (I '' (m ⁻¹' {y})) := sorry

-- Proof sketch: apply the open-set and closed-set bounds for the LDP on `E` to the preimages
-- under `m`; continuity of `m` preserves openness and closedness, and the resulting rate is the
-- infimum of `I` over each singleton fiber.
/-- Theorem 23.16: if a family `μ_ε` of probability measures on `E` satisfies a large deviations
principle with rate function `I`, then its pushforward under a continuous map `m : E → F`
satisfies a large deviations principle with contracted rate function
`y ↦ inf_{x ∈ m⁻¹({y})} I x`. -/
theorem hasLargeDeviationsPrinciple_map_of_continuous
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal)
    (hμ : HasLargeDeviationsPrinciple μ I)
    (m : E → F) (hm : Continuous m) :
    HasLargeDeviationsPrinciple
      (fun ε ↦ ProbabilityMeasure.map (μ ε) hm.measurable.aemeasurable)
      (contractedRateFunction m I) := sorry

end ProbabilityTheory
