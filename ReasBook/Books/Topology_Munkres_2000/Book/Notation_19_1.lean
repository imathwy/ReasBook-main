module

public import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct

universe u v

open scoped CartesianProduct

/- Notation 19.1: When the index type is understood, the Cartesian product of
`A : J → Set X` is written `∏ α, A α`, and its elements are coordinate families
`x : J → X` satisfying `x α ∈ A α` for every `α : J`. -/
#check fun {J : Type u} {X : Type v} (A : J → Set X) ↦ ∏ α, A α

#check fun {J : Type u} {X : Type v} (A : J → Set X) (x : J → X) ↦
  (Set.mem_univ_pi : x ∈ ∏ α, A α ↔ ∀ α, x α ∈ A α)
