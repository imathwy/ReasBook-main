module

public import Mathlib.Topology.Connected.Basic

public section

universe u v

/- Remark 23.1: Connectedness is invariant under homeomorphism. -/
#check Homeomorph.connectedSpace_iff

namespace Homeomorph

/-- The possibly-empty notion of connectedness is also invariant under homeomorphism. -/
theorem preconnectedSpace_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : PreconnectedSpace X ↔ PreconnectedSpace Y := by
  rw [preconnectedSpace_iff_univ, preconnectedSpace_iff_univ]
  constructor
  · intro h
    simpa only [Set.image_univ, e.surjective.range_eq] using
      h.image e e.continuous.continuousOn
  · intro h
    let e' := e.symm
    simpa only [Set.image_univ, e'.surjective.range_eq] using
      h.image e' e'.continuous.continuousOn

end Homeomorph
