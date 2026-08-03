module

public import Mathlib.Topology.UnitInterval

public section

namespace UnitSquare

/-- The counterclockwise parametrization of the four edges of the unit square,
beginning with its bottom edge. Indices at least `3` select the left edge. -/
def edge (index : ℕ) (t : unitInterval) : unitInterval × unitInterval :=
  match index with
  | 0 => (t, 0)
  | 1 => (1, t)
  | 2 => (unitInterval.symm t, 1)
  | _ => (0, unitInterval.symm t)


end UnitSquare
