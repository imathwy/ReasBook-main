module

public import Topology_Munkres_2000.Book.Example_16_2

public section

/-- Remark 16.2: The intrinsic order topology on a subset of `ℝ` need not agree with
the topology it inherits as a subspace of `ℝ`. -/
theorem exists_subspaceTopology_not_orderTopology : ∃ Y : Set ℝ, ¬ OrderTopology Y := by
  refine ⟨isolatedEndpointSet, ?_⟩
  intro h
  have h_open := isolatedPointIsOpenSubspace
  rw [h.topology_eq_generate_intervals] at h_open
  exact isolatedPointNotIsOpenOrder h_open
