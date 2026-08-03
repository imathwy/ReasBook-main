module

public import Mathlib.Topology.Bases

public section

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X} {x : X}

/- Theorem 17.5 (1): A point `x` belongs to `closure A` if and only if every open
set containing `x` intersects `A`. -/
#check (mem_closure_iff :
  x ∈ closure A ↔ ∀ U, IsOpen U → x ∈ U → (U ∩ A).Nonempty)

/- Theorem 17.5 (2): Given a topological basis `𝓑`, a point `x` belongs to
`closure A` if and only if every member of `𝓑` containing `x` intersects `A`. -/
#check fun {𝓑 : Set (Set X)} (h𝓑 : TopologicalSpace.IsTopologicalBasis 𝓑) ↦
  (h𝓑.mem_closure_iff :
    x ∈ closure A ↔ ∀ B ∈ 𝓑, x ∈ B → (B ∩ A).Nonempty)
