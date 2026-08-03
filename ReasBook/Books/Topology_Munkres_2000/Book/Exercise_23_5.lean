module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.Order.DenselyOrdered

public section

universe u

section

variable (X : Type u) [TopologicalSpace X] [DiscreteTopology X]

/- Exercise 23.5 (1): Every discrete topological space is totally disconnected. -/
#check (inferInstance : TotallyDisconnectedSpace X)

end

namespace Rat

/-- The usual topology on `ℚ` is not discrete. -/
theorem not_discreteTopology : ¬ DiscreteTopology ℚ := by
  intro
  have : Subsingleton ℚ := DenselyOrdered.subsingleton_of_discreteTopology
  exact zero_ne_one (this.elim 0 1)

end Rat

/-- Exercise 23.5 (2): The converse fails; the usual topology on `ℚ` is totally
disconnected but is not discrete. -/
theorem ratTotallyDisconnectedNotDiscrete :
    TotallyDisconnectedSpace ℚ ∧ ¬ DiscreteTopology ℚ :=
  ⟨inferInstance, Rat.not_discreteTopology⟩
