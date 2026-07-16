import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω)

/-- The variance-weighted row measure `νₙ` obtained from the `n`-th row by summing the pushforwards
of the measures with density `Xₙ,ᵢ^2`. -/
def varianceWeightedRowMeasure (A : RealRandomVariableArray Ω) (P : Measure Ω) (n : ℕ) :
    Measure ℝ :=
  ∑ i : Fin (A.rowLength n),
    (P.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)

-- Proof sketch: unfold `varianceWeightedRowMeasure`, evaluate the pushforward-with-density sum on
-- the Borel set `{x | ε < |x|}`, and rewrite each summand as the corresponding truncated second
-- moment.
/-- The tail of `νₙ` outside `(-ε, ε)` is the `n`-th Lindeberg truncated second-moment sum. -/
theorem varianceWeightedRowMeasure_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowMeasure P n).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂P := sorry

end

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsCentered P] [A.IsNormed P]

-- Proof sketch: evaluate `varianceWeightedRowMeasure A P n` on `Set.univ`, rewrite each summand
-- as the second moment of `A.entry n i`, use centering to identify it with the variance, and then
-- apply the row-normalization hypothesis.
/-- The variance-weighted row measure has total mass `1` under the centered and normed
hypotheses. -/
theorem varianceWeightedRowMeasure_isProbabilityMeasure
    (n : ℕ) :
    IsProbabilityMeasure (A.varianceWeightedRowMeasure P n) := sorry

/-- The probability measure `νₙ` attached to the `n`-th row by weighting each entry law with
`x^2`. -/
noncomputable def varianceWeightedRowLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨A.varianceWeightedRowMeasure P n, varianceWeightedRowMeasure_isProbabilityMeasure A P n⟩

/-- The underlying measure of `varianceWeightedRowLaw` is `varianceWeightedRowMeasure`. -/
@[simp] theorem varianceWeightedRowLaw_toMeasure (n : ℕ) :
    (A.varianceWeightedRowLaw P n : Measure ℝ) = A.varianceWeightedRowMeasure P n := rfl

end

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsNormed P]

-- Proof sketch: `varianceWeightedRowMeasure_tail_eq` identifies the tails of `νₙ` with the
-- truncated second moments from the Lindeberg condition; `h_lindeberg` supplies the centered
-- instance needed to view each `νₙ` as a probability measure, and vanishing mass outside every
-- neighborhood of `0` yields weak convergence to `δ₀`. Independence is not used here.
/-- Lemma 15.48: if the Lindeberg condition from Theorem 15.43 (i) holds, then the variance-weighted
row laws `νₙ` of a normed array converge weakly to the Dirac probability measure at `0`. -/
theorem varianceWeightedRowLaw_tendsto_diracProba_zero_of_satisfiesLindebergCondition
    (h_lindeberg : A.SatisfiesLindebergCondition P) :
    letI : A.IsCentered P := h_lindeberg.toIsCentered
    Tendsto (fun n ↦ A.varianceWeightedRowLaw P n) atTop (𝓝 (diracProba (0 : ℝ))) := sorry

end

end RealRandomVariableArray
