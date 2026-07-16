import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]
variable [PseudoMetricSpace E] [BorelSpace E]

-- Proof sketch: apply the LDP lower bound to the open balls around `x` and the upper bound for the
-- second rate function to the corresponding closed balls; then let the radius tend to `0` and use
-- lower semicontinuity of both rate functions to get `I x ≤ J x` and `J x ≤ I x`.
/-- Theorem 23.8: if the same positive-parameter family of measures satisfies the large deviations
principle with rate functions `I` and `J`, then the two rate functions coincide pointwise. -/
theorem ldp_rateFunction_unique (μ : PositiveProbabilityFamily E) {I J : E → ENNReal}
    (hI : HasLargeDeviationsPrinciple μ I) (hJ : HasLargeDeviationsPrinciple μ J) :
    I = J := sorry

end ProbabilityTheory
