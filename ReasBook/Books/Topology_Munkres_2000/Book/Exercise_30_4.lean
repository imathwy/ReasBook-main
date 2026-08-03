module

import Mathlib.Topology.Metrizable.Basic

universe u

variable (X : Type u) [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace.MetrizableSpace X]

/- Exercise 30.4. Show that every compact metrizable space `X` has a countable
basis. -/
#check (inferInstance : SecondCountableTopology X)
