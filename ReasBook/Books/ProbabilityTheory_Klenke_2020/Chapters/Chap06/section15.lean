

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_15 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: on each measurable finite-measure set, use the measurable sequence `(fₙ)` to
-- extract a subsequence with summable successive deviation measures, apply Theorem 6.12 (3) to
-- obtain an almost-everywhere limit on that finite piece, and then use the usual
-- triangle-inequality estimate to upgrade the whole sequence to convergence in measure to a
-- globally chosen limit.
/-- Corollary 6.15: In a complete separable metric space, every sequence that is
Cauchy in local `μ`-measure on finite-measure sets converges in local `μ`-measure. -/
theorem cauchyInMeasureOnFiniteMeasureSets_exists_limit
    [TopologicalSpace.SeparableSpace E] [CompleteSpace E]
    (μ : Measure Ω) {fSeq : ℕ → Ω → E}
    (hSeq : ∀ n, Measurable (fSeq n))
    (h_cauchy : CauchyInMeasureOnFiniteMeasureSets μ fSeq) :
    ∃ f : Ω → E, TendstoInMeasureOnFiniteMeasureSets μ fSeq f := sorry
