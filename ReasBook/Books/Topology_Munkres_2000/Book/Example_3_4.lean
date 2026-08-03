module

public import Mathlib.Data.Real.Basic
public import Topology_Munkres_2000.Book.Example_3_4.Fibers

public section

/-- The horizontal line whose second coordinate is `c`. -/
def horizontalLine (c : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = c}

/-- The collection of all horizontal lines in the real plane. -/
def horizontalLines : Set (Set (ℝ × ℝ)) :=
  Set.range horizontalLine

/-- Example 3.4 (1): The equivalence relation on the real plane given by equal
second coordinates. -/
def yCoordinateSetoid : Setoid (ℝ × ℝ) :=
  Setoid.ker Prod.snd

/-- Two points are related by `yCoordinateSetoid` exactly when their second coordinates agree. -/
theorem yCoordinateSetoid_rel_iff (p q : ℝ × ℝ) :
    yCoordinateSetoid p q ↔ p.2 = q.2 :=
  Setoid.ker_def

/-- Example 3.4 (2): The equivalence classes are exactly the horizontal lines. -/
theorem yCoordinateSetoid_classes :
    yCoordinateSetoid.classes = horizontalLines :=
  Setoid.classes_ker_eq_fibers Prod.snd Prod.snd_surjective
