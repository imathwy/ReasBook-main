module

public import Topology_Munkres_2000.Book.Theorem_59_3

public section

namespace StandardSphere

/-- The standard sphere of dimension `k + 2` is simply connected. -/
instance instSimplyConnectedSpace (k : ℕ) :
    SimplyConnectedSpace (StandardSphere (k + 2)) := by
  -- Apply Theorem 59.3 at the automatically admissible dimension `k + 2`.
  exact simplyConnectedSpace_standardSphere (k + 2) (Nat.le_add_left 2 k)

end StandardSphere
