module

import Mathlib.Topology.CompactOpen

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

section

variable [T2Space Y]

/- Exercise 46.6 (1): If `Y` is Hausdorff, then the compact-open topology on
`C(X, Y)` is Hausdorff. -/
#check ContinuousMap.instT2Space

end

section

variable [T3Space Y]

/- Exercise 46.6 (2): If `Y` is regular, then the compact-open topology on
`C(X, Y)` is regular. -/
#check ContinuousMap.instT3Space

end
