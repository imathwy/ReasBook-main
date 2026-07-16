import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Definition_25_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 25.2: the textbook vector space `𝓔` of elementary predictable integrands is the
canonical submodule `MeasureTheory.predictableSimpleProcesses`. -/
recall MeasureTheory.predictableSimpleProcesses

/- Remark 25.6: every textbook elementary integrand `H ∈ 𝓔`, expressed as membership in the
canonical submodule `MeasureTheory.predictableSimpleProcesses`, is predictable in mathlib's
canonical sense. This is exactly
`MeasureTheory.isPredictable_of_mem_predictableSimpleProcesses`. -/
recall MeasureTheory.isPredictable_of_mem_predictableSimpleProcesses
