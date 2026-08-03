module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Category.TopCat.Basic

public section

universe u v

/-- A map is a universal covering map when it is a surjective covering map and its source is
simply connected. -/
def IsUniversalCoveringMap {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace E

namespace IsUniversalCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- A universal covering map is a covering map. -/
theorem isCoveringMap (hp : IsUniversalCoveringMap p) : IsCoveringMap p := hp.1

/-- A universal covering map is surjective. -/
theorem surjective (hp : IsUniversalCoveringMap p) : Function.Surjective p := hp.2.1

/-- The source of a universal covering map is simply connected. -/
theorem simplyConnectedSpace (hp : IsUniversalCoveringMap p) : SimplyConnectedSpace E := hp.2.2

end IsUniversalCoveringMap

/-- A bundled universal covering space of `B`. -/
structure UniversalCovering (B : Type v) [TopologicalSpace B] where
  Total : TopCat.{u}
  proj : Total → B
  isUniversalCoveringMap : IsUniversalCoveringMap proj

namespace UniversalCovering

variable {B : Type v} [TopologicalSpace B]

/-- Bundle a universal covering map as a universal covering space. -/
def of (E : TopCat.{u}) (p : E → B) (hp : IsUniversalCoveringMap p) : UniversalCovering B where
  Total := E
  proj := p
  isUniversalCoveringMap := hp

/-- The projection of a universal covering space is a covering map. -/
theorem isCoveringMap (C : UniversalCovering.{u} B) : IsCoveringMap C.proj :=
  C.isUniversalCoveringMap.isCoveringMap

/-- The projection of a universal covering space is surjective. -/
theorem surjective (C : UniversalCovering.{u} B) : Function.Surjective C.proj :=
  C.isUniversalCoveringMap.surjective

/-- The total space of a universal covering space is simply connected. -/
theorem simplyConnectedSpace (C : UniversalCovering.{u} B) : SimplyConnectedSpace C.Total :=
  C.isUniversalCoveringMap.simplyConnectedSpace

end UniversalCovering
