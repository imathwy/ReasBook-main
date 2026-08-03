module

public import Mathlib.Topology.Order

public section

universe u

variable (X : Type u)

/- Example 12.2 (1): The topology in which every subset of `X` is open is the
discrete topology. -/
#check (⊥ : TopologicalSpace X)
#check discreteTopology_bot X
#check discreteTopology_iff_forall_isOpen

/- Example 12.2 (2): The topology whose only open sets are `∅` and `Set.univ`
is the indiscrete, or trivial, topology. -/
#check (⊤ : TopologicalSpace X)
#check fun U : Set X ↦ TopologicalSpace.isOpen_top_iff U
