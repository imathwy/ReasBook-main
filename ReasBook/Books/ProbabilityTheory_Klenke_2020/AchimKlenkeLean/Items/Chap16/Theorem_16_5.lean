import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

section

-- Proof sketch: for the forward direction, approximate the characteristic exponent of an
-- infinitely divisible law by finite jump measures and use the owner compound-Poisson
-- construction together with weak convergence. For the reverse direction, each compound Poisson
-- law is infinitely divisible, and infinite divisibility is preserved under weak limits.
/-- Theorem 16.5: a probability measure on `ℝ` is infinitely divisible if and only if there is a
sequence of finite jump measures on `ℝ \ {0}` whose canonical compound Poisson laws converge
weakly to it. -/
theorem isInfinitelyDivisible_iff_exists_compoundPoissonApproximation
    (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.IsInfinitelyDivisible μ ↔
      ∃ νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0},
        Tendsto (fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)) atTop (𝓝 μ) := sorry

end
