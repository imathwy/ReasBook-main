module

import Mathlib.Topology.Neighborhoods

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X} {x : X}

/- Remark 17.8: Some mathematicians call `A` a neighborhood of `x` when `A`
contains an open set containing `x`; the book does not use this convention. -/
#check (mem_nhds_iff : A ∈ nhds x ↔ ∃ U ⊆ A, IsOpen U ∧ x ∈ U)
