module

import Mathlib.Topology.Compactness.Lindelof

universe u

variable (X : Type u) [TopologicalSpace X]

/- Definition 30.4. A space is Lindelöf when every open cover has a countable
subcover; the canonical mathlib notion is `LindelofSpace`. -/
#check LindelofSpace X
