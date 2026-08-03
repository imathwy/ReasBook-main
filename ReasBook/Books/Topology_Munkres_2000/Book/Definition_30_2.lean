module

import Mathlib.Topology.Bases

universe u

variable (X : Type u) [TopologicalSpace X]

/- Definition 30.2. A space is second-countable when its topology has a countable
basis; the canonical mathlib notion is `SecondCountableTopology`. -/
#check SecondCountableTopology X
#check TopologicalSpace.IsTopologicalBasis.secondCountableTopology
#check fun [SecondCountableTopology X] ↦ TopologicalSpace.exists_countable_basis X
