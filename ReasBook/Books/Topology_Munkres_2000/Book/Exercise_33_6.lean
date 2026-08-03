module

public import Topology_Munkres_2000.Book.Example_40_1
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Order.T5

public section

universe u

/- Exercise 33.6 (1): A space is perfectly normal if it is normal, every closed
set is a `Gδ` set, and it satisfies the book's `T₁` convention. -/
#check T6Space

/- Exercise 33.6 (2): Every metrizable space is perfectly normal. -/
#check fun {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] ↦
  (inferInstance : T6Space X)

/- Exercise 33.6 (3): Every perfectly normal space is completely normal. -/
#check fun {X : Type u} [TopologicalSpace X] [T6Space X] ↦
  (inferInstance : T5Space X)

/- Exercise 33.6 (4): The closed first-uncountable ordinal is completely normal. -/
#check (inferInstance : T5Space ClosedOmegaOne)

/-- Exercise 33.6 (4): The closed first-uncountable ordinal is not perfectly normal. -/
theorem ClosedOmegaOne.notPerfectlyNormal :
    ¬ T6Space ClosedOmegaOne := by
  intro h
  exact singleton_omega_not_isGδ (h.closed_gdelta isClosed_singleton)
