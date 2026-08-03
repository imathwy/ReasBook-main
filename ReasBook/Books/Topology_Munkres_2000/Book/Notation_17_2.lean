module

import Mathlib.Topology.Neighborhoods

public section

open Filter
open scoped Topology

universe u

/- Notation 17.2. For a sequence `sequence : ℕ → X`, the notation
`sequence n → x` means `Tendsto sequence atTop (𝓝 x)`. In the source this is
used for Hausdorff spaces, where the limit is unique. -/
#check fun {X : Type u} [TopologicalSpace X] (sequence : ℕ → X) (x : X) ↦
  Tendsto sequence atTop (𝓝 x)
