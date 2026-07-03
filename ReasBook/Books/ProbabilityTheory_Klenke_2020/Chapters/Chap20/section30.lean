import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_30 (from Items/Chap20) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 20.30 is a `bridge/view`: the source notation `h(P, τ)` for a
probability-preserving dynamical system is represented in this chapter by the canonical owner
`kolmogorov_sinai_entropy P τ hτ`, specialized from a measure-preserving hypothesis via
`MeasurePreserving.measurable` when needed. -/
recall kolmogorov_sinai_entropy (P : Measure Ω) [IsProbabilityMeasure P]
  (τ : Ω → Ω) (hτ : Measurable τ) : EReal
