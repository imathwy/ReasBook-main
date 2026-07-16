import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [A.IsIndependent μ] [A.IsCentered μ] [A.IsNormed μ]

-- Proof sketch: under the independent, centered, and normed hypotheses, the normalization in
-- `Definition_15_40` is the textbook normalization from Theorem 15.43, so the canonical
-- Lindeberg condition is equivalent to the vanishing of the rowwise truncated second moments for
-- every fixed threshold `ε > 0`.
/-- Under the independent, centered, and normed hypotheses of Theorem 15.43, the canonical
Lindeberg condition from Definition 15.40 is equivalent to the vanishing of the rowwise truncated
second moments for every fixed threshold `ε > 0`. -/
theorem satisfiesLindebergCondition_iff
    :
    A.SatisfiesLindebergCondition μ ↔
      ∀ ⦃ε : ℝ⦄, 0 < ε →
        Tendsto
          (fun n ↦
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ)
          atTop (𝓝 0) := sorry

-- Proof sketch: for `(i) → (ii)`, apply the Lindeberg--Feller characteristic-function argument to
-- the independent centered normed row sums to obtain convergence in distribution to the standard
-- Gaussian, and use the same truncation estimates to deduce the null-array property. For
-- `(ii) → (i)`, combine weak convergence of the laws of the row sums with the null-array
-- hypothesis and the preceding truncation criterion to recover the canonical Lindeberg condition.
/-- Theorem 15.43: for an independent centered and normed array of real random variables, the
Lindeberg condition is equivalent to saying that the array is null and that the laws of the row
sums converge weakly to the standard Gaussian law `𝒩(0, 1)`. -/
theorem lindeberg_feller_central_limit_theorem
    :
    A.SatisfiesLindebergCondition μ ↔
      A.IsNull μ ∧
        Tendsto (A.rowSumLaw μ) atTop
          (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := sorry

end

end RealRandomVariableArray
