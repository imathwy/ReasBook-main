module

import Mathlib.Topology.MetricSpace.Completion

universe u

open UniformSpace

variable (X : Type u) [MetricSpace X]

/- Theorem 43.3: Every metric space embeds isometrically into a complete metric space,
namely its canonical completion. -/
#check (Completion.coe_isometry : Isometry (Completion.coe' : X → Completion X))
#check (inferInstance : CompleteSpace (Completion X))
