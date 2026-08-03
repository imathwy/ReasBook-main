module

public import Mathlib.Topology.Separation.Basic

public section

namespace Multiplicative

/-- The multiplicative synonym inherits the `T₁` property of its underlying space. -/
instance instT1Space {X : Type*} [TopologicalSpace X] [T1Space X] :
    T1Space (Multiplicative X) :=
  inferInstanceAs (T1Space X)

end Multiplicative
