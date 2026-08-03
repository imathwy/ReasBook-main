module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty
public import Mathlib.Order.WellFounded

import Topology_Munkres_2000.Book.Definition_10_1

public section

universe u

/-- Exercise 10.1: Every well-ordered linear type has the least upper bound property. -/
theorem wellFoundedLT_leastUpperBoundProperty
    (α : Type u) [LinearOrder α] [WellFoundedLT α] : LeastUpperBoundProperty α := by
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro s hs hb
  obtain ⟨a, ha⟩ := hb
  obtain ⟨m, hm⟩ := wellFoundedLT_iff_exists_isLeast.mp inferInstance
    (upperBounds s) ⟨a, ha⟩
  exact ⟨m, hm⟩
