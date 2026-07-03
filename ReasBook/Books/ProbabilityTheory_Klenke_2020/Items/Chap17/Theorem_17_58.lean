import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_57
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

-- Proof sketch: for the forward implication, integrate every bounded measurable monotone test
-- function against the coupling `φ` and use that `f x₁ ≤ f x₂` on `{z | z.1 ≤ z.2}`.
-- For the reverse implication, apply the multivariate Strassen theorem for the coordinatewise
-- order on `ℝ^d` to obtain a coupling whose mass is concentrated on the ordered set.
/-- Theorem 17.58: on `ℝ^d`, modeled as `Fin d → ℝ`, one probability measure is below another in
stochastic order if and only if there is a coupling of the two laws that gives mass `1` to the
set of ordered pairs `(x₁, x₂)` with `x₁ ≤ x₂` coordinatewise. -/
theorem stochasticLE_iff_exists_ordered_coupling {d : ℕ}
    (μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)) :
    StochasticLE μ1 μ2 ↔
      ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
        IsCoupling φ μ1 μ2 ∧
          (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))) {z | z.1 ≤ z.2} = 1 := sorry

-- Proof sketch: rewrite the source-facing mass-`1` statement using the probability-measure
-- equivalence between a measurable event having measure `1` and holding almost everywhere.
/-- The ordered-coupling characterization of stochastic order can equivalently be stated by
requiring the coupled coordinates to satisfy `x₁ ≤ x₂` almost everywhere. This is the canonical
owner-style form used by later coupling constructions in the chapter. -/
theorem stochasticLE_iff_exists_ae_ordered_coupling {d : ℕ}
    (μ1 μ2 : ProbabilityMeasure (Fin d → ℝ)) :
    StochasticLE μ1 μ2 ↔
      ∃ φ : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
        IsCoupling φ μ1 μ2 ∧
          ∀ᵐ z ∂ (φ : Measure ((Fin d → ℝ) × (Fin d → ℝ))), z.1 ≤ z.2 := sorry

end ProbabilityTheory
