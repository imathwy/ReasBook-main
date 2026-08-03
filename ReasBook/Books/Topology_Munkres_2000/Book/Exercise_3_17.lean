module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty
import Topology_Munkres_2000.Book.Exercise_3_13
import Topology_Munkres_2000.Book.Exercise_3_14

public section

universe u

/-- Exercise 3.17: A linear order has the least upper bound property if and only if
it has the greatest lower bound property. -/
theorem leastUpperBoundProperty_iff_greatestLowerBoundProperty
    (α : Type u) [LinearOrder α] :
    LeastUpperBoundProperty α ↔ GreatestLowerBoundProperty α :=
  ⟨leastUpperBoundProperty_implies_greatestLowerBoundProperty α,
    greatestLowerBoundProperty_implies_leastUpperBoundProperty α⟩
