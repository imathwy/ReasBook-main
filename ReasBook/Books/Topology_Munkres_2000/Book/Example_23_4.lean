module

public import Mathlib.Topology.Instances.RatLemmas

public section

/- Example 23.4 (1): With its usual topology, `ℚ` is totally disconnected, so its
connected subspaces contain at most one point. -/
#check (inferInstance : TotallyDisconnectedSpace ℚ)

/-- Example 23.4 (2): With its usual topology, `ℚ` is not connected. -/
theorem rat_not_connected : ¬ ConnectedSpace ℚ := by
  intro h
  have hsub : (Set.univ : Set ℚ).Subsingleton :=
    TotallyDisconnectedSpace.isTotallyDisconnected_univ Set.univ (Set.subset_univ _)
      h.toPreconnectedSpace.isPreconnected_univ
  exact zero_ne_one (hsub (Set.mem_univ 0) (Set.mem_univ 1))
