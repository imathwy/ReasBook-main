module

public import Topology_Munkres_2000.Book.Theorem_45_4.ProperTarget

import Mathlib.Topology.Bornology.Hom
import Mathlib.Topology.MetricSpace.Bounded

public section

universe u v

namespace BoundedContinuousFunction

/-- For a proper metric target, a family of continuous maps from a compact space is compact in
the uniform topology exactly when it is closed, bounded, and equicontinuous. -/
theorem isCompact_iff_isClosed_isBounded_equicontinuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X]
    [MetricSpace Y] [ProperSpace Y] (𝓕 : Set (X →ᵇ Y)) :
    IsCompact 𝓕 ↔ IsClosed 𝓕 ∧ Bornology.IsBounded 𝓕 ∧
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) := by
  constructor
  · intro h_compact
    have h_compact_closure : IsCompact (closure 𝓕) := by
      simpa [h_compact.isClosed.closure_eq] using h_compact
    have h_equicontinuous :=
      (isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕).1 h_compact_closure
    exact ⟨h_compact.isClosed, h_compact.isBounded, h_equicontinuous.1⟩
  · rintro ⟨h_closed, h_bounded, h_equicontinuous⟩
    have h_pointwise : PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y)) :=
      pointwiseBounded_iff.2 fun x ↦ by
        have h_image := (lipschitz_eval_const x).isBounded_image h_bounded
        simpa [Set.image_eq_range] using h_image
    have h_compact_closure :=
      (isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕).2
        ⟨h_equicontinuous, h_pointwise⟩
    simpa [h_closed.closure_eq] using h_compact_closure

end BoundedContinuousFunction
