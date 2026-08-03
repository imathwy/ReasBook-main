module

import Mathlib.Topology.Defs.Basic

/- Remark 17.3: Mathlib defines `interior A` as
`⋃₀ {U | IsOpen U ∧ U ⊆ A}` and `closure A` as
`⋂₀ {C | IsClosed C ∧ A ⊆ C}`. -/
#check interior
#check closure
