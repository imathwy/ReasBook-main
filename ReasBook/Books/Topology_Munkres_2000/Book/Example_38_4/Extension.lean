module

public import Topology_Munkres_2000.Book.Definition_29_2.Compactification
public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u v w

namespace Compactification

variable {X : Type u} [TopologicalSpace X]

/-- A map extends continuously along a compactification when it is the restriction of a
continuous map on the compactifying space. -/
def Extends (C : Compactification.{u, v} X) {Y : Type w} [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∃ g : ContinuousMap C Y, ∀ x : X, g (C x) = f x

/-- A witness that `f` extends along `C` is precisely a continuous map agreeing with `f` on
the embedded copy of `X`. -/
theorem extends_iff (C : Compactification.{u, v} X) {Y : Type w} [TopologicalSpace Y]
    (f : X → Y) :
    C.Extends f ↔ ∃ g : ContinuousMap C Y, ∀ x : X, g (C x) = f x :=
  Iff.rfl

end Compactification

end
