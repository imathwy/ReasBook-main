import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

/- Remark 13.32: every singleton family of finite measures is weakly compact in the ambient weak
topology on `FiniteMeasure E`, so the converse direction of Prohorov's theorem cannot force
tightness without an additional hypothesis; the Polish hypothesis supplies that extra input. This
compactness part is the general theorem `isCompact_singleton`. -/
recall isCompact_singleton

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/- The Polish-space tightness input is the canonical owner theorem
`MeasureTheory.isTightMeasureSet_singleton`; applied to a finite measure `μ`, it yields tightness
of `{(μ : Measure E)}` in `Measure E`. -/
recall MeasureTheory.isTightMeasureSet_singleton
