module

public import Topology_Munkres_2000.Book.Definition_29_2.Compactification
public import Topology_Munkres_2000.Book.Exercise_24_1.UnitInterval
public import Mathlib.Topology.Order.Compact

public section

open Set

namespace OpenUnitInterval

/-- The compactification of `(0, 1)` by the closed interval `[0, 1]`. -/
@[expose]
def closedUnitIntervalCompactification : Compactification (Ioo (0 : ℝ) 1) :=
  Compactification.of (Icc (0 : ℝ) 1) UnitInterval.openInClosed
    UnitInterval.isDenseEmbedding_openInClosed

/-- The closed-unit-interval compactification uses the canonical inclusion map. -/
theorem closedUnitIntervalCompactification_apply (x : Ioo (0 : ℝ) 1) :
    closedUnitIntervalCompactification x = UnitInterval.openInClosed x := rfl


end OpenUnitInterval

end
