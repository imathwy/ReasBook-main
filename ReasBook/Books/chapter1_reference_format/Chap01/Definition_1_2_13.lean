import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u

variable (K : Type u) [NormedField K]

/- Definition 1.2.13: a normed field carries the metric induced by its norm, namely
`d(x,y) = ‖x - y‖`; its completeness is the canonical predicate `CompleteSpace K`, equivalently
every Cauchy sequence for this metric converges to a limit in `K`. -/
#check (CompleteSpace K)

section

variable {K : Type u} [NormedField K]

/-- A normed field is complete exactly when every Cauchy sequence in its norm-induced metric
converges. -/
theorem chapter1ReferenceFormat_completeSpace_iff_cauchySeq_tendsto :
    CompleteSpace K ↔ ∀ u : ℕ → K, ∀ (_ : CauchySeq u), ∃ a : K, Tendsto u atTop (𝓝 a) := by
  constructor
  · intro hK u hu
    let _ : CompleteSpace K := hK
    exact cauchySeq_tendsto_of_complete hu
  · intro h
    exact Metric.complete_of_cauchySeq_tendsto h

end
