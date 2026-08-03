module

public import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct

universe u v

open scoped CartesianProduct

/- Definition 19.4: The Cartesian product of a family `A : J → Set X` is
`∏ α, A α`, the set of functions whose value at each index `α` lies in `A α`. -/
#check fun {J : Type u} {X : Type v} (A : J → Set X) ↦ ∏ α, A α

#check fun {J : Type u} {X : Type v} (A : J → Set X) (x : J → X) ↦
  (Set.mem_univ_pi : x ∈ ∏ α, A α ↔ ∀ α, x α ∈ A α)
