module

public import Mathlib.Topology.Separation.Lemmas

public section

universe u

namespace ConnectedSpace

/-- Exercise 27.4: A connected metric space with more than one point is uncountable. -/
instance uncountable_of_metricSpace {X : Type u} [MetricSpace X] [ConnectedSpace X]
    [Nontrivial X] : Uncountable X := by
  rw [← not_countable_iff]
  intro hX
  have h_univ : (Set.univ : Set X).Countable := Set.countable_univ_iff.2 hX
  have h_subsingleton : (Set.univ : Set X).Subsingleton :=
    h_univ.isTotallyDisconnected Set.univ subset_rfl isPreconnected_univ
  exact not_subsingleton X (Set.subsingleton_of_univ_subsingleton h_subsingleton)

end ConnectedSpace
