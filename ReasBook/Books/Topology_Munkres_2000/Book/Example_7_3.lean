module

public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite
import Topology_Munkres_2000.Book.Definition_7_1
import Mathlib.Data.Rat.Denumerable
public import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Order.Interval.Set.Infinite

public section

/-- Example 7.3. The set of positive rational numbers is countably infinite. -/
theorem positiveRationals_countablyInfinite : (Set.Ioi (0 : ℚ)).CountablyInfinite := by
  -- Combine inherited countability with infinitude of the upper interval.
  exact (Set.countablyInfinite_iff_countable_and_infinite _).2
    ⟨Set.to_countable _, Set.Ioi_infinite 0⟩
