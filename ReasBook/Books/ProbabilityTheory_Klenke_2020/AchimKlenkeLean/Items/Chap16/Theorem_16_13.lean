import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_39
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u v

noncomputable section

open RealRandomVariableArray

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']
variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsIndependent P] [A.IsNull P]

-- Proof sketch: `hS.tendsto` identifies the law of `S` as the weak limit of the owner-level
-- row-sum laws `A.rowSumLaw P`. Apply the array-to-law bridge furnished by Theorem 16.12 to
-- that limiting law, then translate back to the random-variable formulation using
-- `isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible`.
/-- Theorem 16.13: if the row sums of an independent null array of real random variables converge
in distribution to a real random variable `S`, then `S` is infinitely divisible. -/
theorem null_array_limit_isInfinitelyDivisible
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q) :
    IsInfinitelyDivisibleRandomVariable Q S := sorry

end
