module

import Topology_Munkres_2000.Book.Definition_10_4.MinimalOrder
import Topology_Munkres_2000.Book.Exercise_41_2
import Mathlib.Topology.Metrizable.Urysohn

public section

/- Exercise 42.2 (1): The section of `S_Ω` by `x` has a countable basis. -/
#check fun (x : OpenOmegaOne) ↦
  (inferInstance : SecondCountableTopology (Set.Iio x))

/- Exercise 42.2 (2): Hence the section of `S_Ω` by `x` is metrizable. -/
#check fun (x : OpenOmegaOne) ↦
  (inferInstance : TopologicalSpace.MetrizableSpace (Set.Iio x))

/- Exercise 42.2 (3): The open first-uncountable ordinal `S_Ω` is not
paracompact. -/
#check OpenOmegaOne.notParacompact
