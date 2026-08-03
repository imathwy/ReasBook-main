module

public import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct

universe u v

open scoped CartesianProduct

/- Notation 19.3: The coordinate-restricted product of a family
`U : (α : J) → Set (X α)` is `∏ α, U α`. A coordinate is unrestricted
when `U α = Set.univ`. -/
#check fun {J : Type u} {X : J → Type v} (U : (α : J) → Set (X α)) ↦
  ∏ α, U α

#check fun {J : Type u} {X : J → Type v} (U : (α : J) → Set (X α))
    (x : (α : J) → X α) ↦
  (Set.mem_univ_pi : x ∈ ∏ α, U α ↔ ∀ α, x α ∈ U α)
