import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

universe u

namespace MeasureTheory
namespace FiniteMeasure

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

-- Proof sketch: weak convergence implies tightness by Prohorov's theorem and gives convergence of
-- the integrals of every bounded continuous test function, hence of any separating subfamily. For
-- the converse, combine tightness with relative sequential compactness, pass to weakly convergent
-- subsequences, and use the separating family to identify every subsequential limit with `μ`.
/-- Theorem 13.34: for subprobability finite measures on a Polish space, weak convergence to `μ`
is equivalent to tightness of the sequence together with convergence of the integrals on some
separating family of bounded continuous real-valued test functions. -/
theorem tendsto_iff_isTightFamily_and_exists_separating_boundedContinuousFamily
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E) (hμ : μ.mass ≤ 1)
    (hμs : ∀ n, (μs n).mass ≤ 1) :
    Tendsto μs atTop (𝓝 μ) ↔
      IsTightMeasureSet (((↑) : FiniteMeasure E → Measure E) '' Set.range μs) ∧
        ∃ 𝒞 : Set (E →ᵇ ℝ),
          IsSeparatingFamilyFor
              (((↑) : FiniteMeasure E → Measure E) ''
                {ν : FiniteMeasure E | ν.mass ≤ 1})
              (((↑) : (E →ᵇ ℝ) → E → ℝ) '' 𝒞) ∧
            ∀ ⦃f : E →ᵇ ℝ⦄, f ∈ 𝒞 →
              Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                (𝓝 (∫ x, f x ∂(μ : Measure E))) := sorry

end FiniteMeasure
end MeasureTheory
