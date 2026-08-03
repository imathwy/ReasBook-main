module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Defs

public section

universe u

namespace Set

/- Definition 61.1: `Set.Separates` says that the complement of a subset is not
preconnected, while `Set.SeparatesInto` records the number of its connected components. -/

/-- Definition 61.1 (1). A subset separates a topological space when its complement is not
preconnected. -/
def Separates {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  ¬ PreconnectedSpace (Aᶜ : Set X)

/-- Definition 61.1 (2). A subset separates a topological space into `n` components when its
complement has exactly `n` connected components. -/
def SeparatesInto {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ) : Prop :=
  Cardinal.mk (ConnectedComponents (Aᶜ : Set X)) = n

end Set
