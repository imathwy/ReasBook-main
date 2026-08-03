module

public import Mathlib.Topology.ExtremallyDisconnected

public section

universe u

namespace StoneCech

/-- The Stone–Čech compactification of a discrete space is extremally disconnected. -/
instance instExtremallyDisconnected
    (X : Type u) [TopologicalSpace X] [DiscreteTopology X] :
    ExtremallyDisconnected (StoneCech X) :=
  CompactT2.Projective.extremallyDisconnected StoneCech.projective

end StoneCech
