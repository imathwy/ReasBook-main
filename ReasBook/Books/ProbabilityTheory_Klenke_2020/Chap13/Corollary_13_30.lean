import Mathlib
import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory MeasureTheory.FiniteMeasure

universe u

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [CompactSpace E]

-- Proof sketch: by Prokhorov compactness on a compact space, the set of finite measures of mass at
-- most `1` is compact in the canonical weak topology on `FiniteMeasure E`; since this topology is
-- metrizable for compact metric `E`, compactness yields sequential compactness.
/-- Corollary 13.30 (1): for a compact metric space `E`, the textbook set `\mathcal{M}_{\le 1}(E)`
of sub-probability measures is weakly sequentially compact, viewed canonically as the set of finite
measures on `E` with total mass at most `1`. -/
theorem subprobabilityMeasures_isSeqCompact :
    IsSeqCompact {μ : FiniteMeasure E | μ.mass ≤ 1} := sorry

/- Corollary 13.30 (2): for a compact metric space `E`, the textbook set `\mathcal{M}_1(E)` of
probability measures is weakly sequentially compact; in mathlib this is the canonical weak space
`ProbabilityMeasure E`, carrying the corresponding `SeqCompactSpace` instance. -/
#check (inferInstance : SeqCompactSpace (ProbabilityMeasure E))

end
