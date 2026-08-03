module

public import Mathlib.Order.Directed
public import Mathlib.Order.SupClosed
public import Mathlib.Topology.Sets.Closeds

public section

universe u

/- Exercise 3.99.1 (1): Every linearly ordered type is a directed set. -/
#check fun {α : Type u} [LinearOrder α] ↦ (inferInstance : IsDirectedOrder α)

/- Exercise 3.99.1 (2): The collection of all subsets of `S`, ordered by inclusion,
is a directed set. -/
#check fun {S : Type u} ↦ (inferInstance : IsDirectedOrder (Set S))

/- Exercise 3.99.1 (3): A family of subsets closed under binary intersections is directed
when ordered by reverse inclusion. -/
#check fun {S : Type u} {𝒜 : Set (Set S)} (h𝒜 : InfClosed 𝒜) ↦
  h𝒜.codirectedOn.isCodirectedOrder

/- Exercise 3.99.1 (4): The collection of all closed subsets of `X`, ordered by inclusion,
is a directed set. -/
#check fun {X : Type u} [TopologicalSpace X] ↦
  (inferInstance : IsDirectedOrder (TopologicalSpace.Closeds X))
