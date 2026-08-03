module

public import Topology_Munkres_2000.Book.Exercise_73_2.CWComplex
public import Topology_Munkres_2000.Book.Exercise_73_4.PerfectMap

public section

/-- Exercise 73.4: Every finite two-dimensional CW complex constructed in Exercise 73.2 is
metrizable. -/
instance TwoDimensionalCWComplex.instMetrizableSpaceSpace {n m : ℕ}
    (f : TwoDimensionalCWComplex.AttachingMap n m) :
    TopologicalSpace.MetrizableSpace (TwoDimensionalCWComplex.Space f) :=
  TwoDimensionalCWComplex.quotientMap_isPerfectMap f |>.metrizableSpace
