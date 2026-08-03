module

public import Topology_Munkres_2000.Book.Exercise_55_1.FixedPoint
public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import Topology_Munkres_2000.Book.Theorem_55_6

public section

/-- Exercise 55.1: If `A` is a retract of the closed two-dimensional unit disk,
then every continuous self-map of `A` has a fixed point. -/
theorem closedUnitDiskRetract_exists_fixedPoint
    {A : Set ClosedUnitDisk} (hA : Set.IsRetract A)
    (f : C(A, A)) : ∃ x, Function.IsFixedPt f x :=
  hA.exists_fixedPoint ClosedUnitDisk.exists_fixedPoint f
