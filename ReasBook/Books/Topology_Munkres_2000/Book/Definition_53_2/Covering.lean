module

public import Mathlib.Topology.Covering.Basic

public section

universe u v

/-- A surjective covering map is a covering map in Munkres's convention. -/
def IsSurjectiveCoveringMap {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  IsCoveringMap p ∧ Function.Surjective p

namespace IsSurjectiveCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- A surjective covering map is a covering map. -/
theorem isCoveringMap (hp : IsSurjectiveCoveringMap p) : IsCoveringMap p := hp.1

/-- A surjective covering map is surjective. -/
theorem surjective (hp : IsSurjectiveCoveringMap p) : Function.Surjective p := hp.2

end IsSurjectiveCoveringMap

/-- The specification of a surjective covering map in terms of mathlib's covering-map
convention. -/
theorem isSurjectiveCoveringMap_iff {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) :
    IsSurjectiveCoveringMap p ↔ IsCoveringMap p ∧ Function.Surjective p :=
  Iff.rfl
