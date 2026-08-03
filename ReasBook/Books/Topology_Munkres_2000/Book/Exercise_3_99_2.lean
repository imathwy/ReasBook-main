module

public import Mathlib.Order.Bounds.Basic

public section

universe u

namespace IsCofinal

/-- Exercise 3.99.2: A cofinal subset `K` of a directed preordered type `J`,
viewed as a subtype with its inherited order, is itself directed. -/
theorem isDirectedOrder {J : Type u} [Preorder J] [IsDirectedOrder J]
    {K : Set J} (hK : IsCofinal K) : IsDirectedOrder K :=
  DirectedOn.isDirectedOrder <|
    DirectedOn.of_isCofinalFor directedOn_univ (Set.subset_univ K) (fun x _ ↦ hK x)

end IsCofinal
