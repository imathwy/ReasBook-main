module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty

public section

universe u

/-- Exercise 3.13: If a linear order has the least upper bound property, then it
has the greatest lower bound property. -/
theorem leastUpperBoundProperty_implies_greatestLowerBoundProperty
    (α : Type u) [LinearOrder α] (h : LeastUpperBoundProperty α) :
    GreatestLowerBoundProperty α := by
  apply GreatestLowerBoundProperty.of_exists_isGLB
  intro s hs hb
  obtain ⟨a, ha⟩ := h.exists_isLUB (lowerBounds s) hb hs.bddAbove_lowerBounds
  exact ⟨a, isLUB_lowerBounds.mp ha⟩
