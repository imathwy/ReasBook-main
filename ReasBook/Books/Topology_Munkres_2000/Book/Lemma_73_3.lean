module

public import Topology_Munkres_2000.Book.Exercise_31_6.ClosedMap

public section

universe u v

namespace Topology.IsQuotientMap

/-- Lemma 73.3: A closed quotient map carries normality in the book's sense
from its domain to its codomain. -/
theorem t4Space {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    [T4Space E] {π : E → X} (hπ : IsQuotientMap π) (hπ_closed : IsClosedMap π) : T4Space X :=
  hπ_closed.t4Space hπ.continuous hπ.surjective

end Topology.IsQuotientMap
