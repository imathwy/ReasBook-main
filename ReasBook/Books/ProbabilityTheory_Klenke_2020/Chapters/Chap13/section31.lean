

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_13_31 (from Items/Chap13) -/
open MeasureTheory MeasureTheory.FiniteMeasure Set

universe u

section

variable {E : Type u} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]
  [BorelSpace E]
  [LocallyCompactSpace E]

-- Proof sketch: exhaust `E` by relatively compact open sets, apply the preceding Prohorov-type
-- compactness result to the restricted owner family of subprobability finite measures on the
-- compact closures, and diagonalize the resulting subsequences. The compatibility of the
-- restricted limits reconstructs a vague limit in the image of the canonical bridge
-- `toRadonMeasure : FiniteMeasure E → RadonMeasure E`.
/-- Corollary 13.31: if `E` is a locally compact separable metric space, then the textbook space
`𝓜_{≤ 1}(E)` of sub-probability measures is sequentially compact for the vague topology, viewed as
the image under `toRadonMeasure` of the canonical owner set
`{μ : FiniteMeasure E | μ.mass ≤ 1}`. -/
theorem subProbabilityMeasureSpace_isSeqCompact_vagueTopology :
    IsSeqCompact (toRadonMeasure '' {μ : FiniteMeasure E | μ.mass ≤ 1}) := sorry

end
