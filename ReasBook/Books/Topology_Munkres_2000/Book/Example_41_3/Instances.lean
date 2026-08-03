module

public import Topology_Munkres_2000.Book.Exercise_29_7.Compactification

public section

universe u

/- The closed first-uncountable ordinal is compact. -/
#check (inferInstance : CompactSpace ClosedOmegaOne.{u})
