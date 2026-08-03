module

import Mathlib.Topology.Compactness.Lindelof

universe u

/- Theorem 30.3 (1). A second-countable space is Lindelöf. -/
#check fun (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] ↦
  (inferInstance : LindelofSpace X)

/- Theorem 30.3 (2). A second-countable space is separable. -/
#check fun (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] ↦
  (inferInstance : TopologicalSpace.SeparableSpace X)
