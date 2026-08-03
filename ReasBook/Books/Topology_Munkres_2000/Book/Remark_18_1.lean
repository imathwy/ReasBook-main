module

import Mathlib.Topology.Defs.Basic

open scoped Topology

universe u v

variable {X : Type u} {Y : Type v}
variable (tX : TopologicalSpace X) (tY : TopologicalSpace Y) (f : X → Y)

/- Remark 18.1: Continuity of `f : X → Y` is relative to the specified
topologies `tX` and `tY` on `X` and `Y`, respectively. Mathlib expresses this
as `Continuous[tX, tY] f`. -/
#check Continuous[tX, tY] f
