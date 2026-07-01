import AchimKlenkeLean.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

-- Proof sketch: by Lemma 15.44, the Lindeberg condition implies the null-array property, so the
-- entry characteristic functions are uniformly close to `1`; then use the rowwise independence to
-- compare the row characteristic function with the product of the entry characteristic functions,
-- apply the quadratic logarithm estimate termwise, and combine it with Lemma 15.45.
/-- Lemma 15.46: under the standing setup of Theorem 15.43 and its item (i) Lindeberg condition,
the logarithm of the row characteristic function is asymptotically equal to the sum of the
first-order terms `φₙ,ᵢ(t) - 1`. -/
theorem rowSumLaw_log_sub_sum_entryCharFun_tendsto_zero
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [A.IsIndependent μ] [A.IsNormed μ]
    (h_lindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦
        ‖Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) t) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖)
      atTop
      (𝓝 0) := sorry

end RealRandomVariableArray
