module

import Mathlib.Topology.Metrizable.Basic

public section

universe u

variable (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]

/- Remark 30.1. Every metrizable topological space satisfies the first
countability axiom. -/
#check (inferInstance : FirstCountableTopology X)
