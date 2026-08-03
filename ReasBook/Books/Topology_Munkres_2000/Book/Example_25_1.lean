module

public import Topology_Munkres_2000.Book.Example_23_4

public section

namespace Rat

/- Example 25.1 (1): each connected component of `ℚ` consists of a single point. -/
#check (connectedComponent_eq_singleton : ∀ q : ℚ, connectedComponent q = {q})

/-- Example 25.1 (2): no connected component of `ℚ` is open in `ℚ`. -/
theorem connectedComponent_not_isOpen (q : ℚ) :
    ¬ IsOpen (connectedComponent q) := by
  rw [connectedComponent_eq_singleton]
  exact not_isOpen_singleton q

end Rat
