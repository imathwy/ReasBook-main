module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Topology_Munkres_2000.Book.Example_16_3.OrderedSquare
public import Topology_Munkres_2000.Book.Exercise_3_15

public section

namespace OrderedSquare

/-- The ordered square is a linear continuum. -/
instance instLinearContinuum : LinearContinuum Iₒ² where
  -- Density follows from the canonical lexicographic order instances.
  toDenselyOrdered := inferInstanceAs (DenselyOrdered LexUnitSquare)
  -- Completeness is the closed-square case of lexicographic completeness.
  leastUpperBoundProperty := lexClosedClosed_leastUpperBoundProperty

end OrderedSquare
