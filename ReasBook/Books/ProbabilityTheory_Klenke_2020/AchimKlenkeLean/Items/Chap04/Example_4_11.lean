import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap04.Definition_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- Example 4.11: On a discrete measurable space with canonical weighted counting measure
`Measure.count.withDensity α`, an `EReal`-valued function is integrable if and only if the
weighted absolute-value series `∑' ω, |f ω| α ω` is finite. -/
theorem weightedDiscreteMeasure_integrable_iff {f : Ω → EReal} (α : Ω → ℝ≥0∞) :
    erealIntegrable f (Measure.count.withDensity α) ↔
      (∑' ω, (f ω).abs * α ω) < ⊤ := by
  rw [erealIntegrable, lintegral_withDensity_eq_lintegral_mul _ Measurable.of_discrete
    Measurable.of_discrete,
    lintegral_count]
  simpa [mul_comm] using
    (and_iff_right (show Measurable f from Measurable.of_discrete))

-- Proof sketch: expand `erealIntegral` into the difference of the lower integrals of the positive
-- and negative parts, compute each lower integral on `Measure.count.withDensity α` as a weighted
-- series over the atoms, and recombine the resulting series into the weighted sum of the values.
/-- For the canonical weighted counting measure `Measure.count.withDensity α`, the textbook
extended-real integral equals the weighted sum of the atomic values whenever `f` is integrable. -/
theorem weightedDiscreteMeasure_erealIntegral_eq_tsum {f : Ω → EReal} (α : Ω → ℝ≥0∞)
    (hf : erealIntegrable f (Measure.count.withDensity α)) :
    erealIntegral f (Measure.count.withDensity α) hf.defined =
      ∑' ω, α ω * f ω := sorry
