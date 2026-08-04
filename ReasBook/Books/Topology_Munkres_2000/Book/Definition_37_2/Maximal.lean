module

public import Topology_Munkres_2000.Book.Definition_26_5
public import Mathlib.Order.Minimal

public section

open Set

universe u

/-- A family of subsets is maximal with respect to the finite intersection property. -/
abbrev IsMaximalFiniteIntersection {X : Type u} (𝒟 : Set (Set X)) : Prop :=
  Maximal Set.FiniteIntersectionProperty 𝒟
