module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Compactification.StoneCech

public section

universe u

namespace StoneCech

/-- The Stone–Čech compactification of a connected space is connected. -/
instance instConnectedSpace (X : Type u) [TopologicalSpace X] [ConnectedSpace X] :
    ConnectedSpace (StoneCech X) where
  isPreconnected_univ :=
    (denseRange_stoneCechUnit.preconnectedSpace continuous_stoneCechUnit).isPreconnected_univ
  toNonempty := Nonempty.map stoneCechUnit inferInstance

end StoneCech

end
