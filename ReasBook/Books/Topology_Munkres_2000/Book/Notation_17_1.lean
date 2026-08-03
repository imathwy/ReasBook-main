module

public import Mathlib.Topology.Closure

public section

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X} {x : X}

/- Notation 17.1: For a subset `A` of a topological space `X`, a point `x`
belongs to `closure A` if and only if every neighborhood of `x` intersects `A`. -/
#check (mem_closure_iff :
  x ∈ closure A ↔ ∀ U, IsOpen U → x ∈ U → (U ∩ A).Nonempty)
