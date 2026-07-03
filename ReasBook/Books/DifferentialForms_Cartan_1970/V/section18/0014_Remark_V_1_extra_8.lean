import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u v

-- Semantic recall note: the canonical owners here are `isSeqClosed_iff_isClosed` and
-- `tendsto_nhds_iff_seq_tendsto`; this file keeps only thin source-facing bridges to those
-- sequential-space interfaces.
/-- Remark V.1-extra-8 (1), in canonical sequential-space form: a subset is closed if and only if
it contains every limit of every sequence of its points. -/
theorem isClosed_iff_seq_limit_mem
    {E : Type u} [TopologicalSpace E] [SequentialSpace E] {A : Set E} :
    IsClosed A ↔
      ∀ ⦃x : E⦄ ⦃u : ℕ → E⦄,
        (∀ n : ℕ, u n ∈ A) → Tendsto u atTop (𝓝 x) → x ∈ A := by
  constructor
  · intro h x u hu hux
    exact h.isSeqClosed hu hux
  · intro h
    have hA : IsSeqClosed A := fun {_u} {_x} hu hux ↦ h hu hux
    exact isSeqClosed_iff_isClosed.mp hA

/-- Remark V.1-extra-8 (2), in canonical Fréchet-Urysohn form: continuity at a point is equivalent
to preservation of limits of sequences converging to that point. -/
theorem continuousAt_iff_seq_tendsto
    {E : Type u} {E' : Type v} [TopologicalSpace E] [FrechetUrysohnSpace E]
    [TopologicalSpace E'] {f : E → E'} {x : E} :
    ContinuousAt f x ↔
      ∀ u : ℕ → E,
        Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 (f x)) := by
  simpa [ContinuousAt] using tendsto_nhds_iff_seq_tendsto
