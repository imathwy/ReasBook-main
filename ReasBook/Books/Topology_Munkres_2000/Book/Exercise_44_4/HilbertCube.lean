module

public import Topology_Munkres_2000.Book.Exercise_25_6.WeaklyLocallyConnected
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.UnitInterval

public section

open Set Topology

universe u v

/-- Helper for Exercise 44.4: a product of connected, locally connected spaces is weakly
locally connected. -/
theorem weaklyLocallyConnectedSpacePiOfConnected
    {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, ConnectedSpace (X i)] [∀ i, LocallyConnectedSpace (X i)] :
    WeaklyLocallyConnectedSpace (∀ i, X i) := by
  refine ⟨fun x ↦ (weaklyLocallyConnectedAt_iff x).mpr ?_⟩
  intro U hU
  -- Refine the neighborhood to a cylinder restricting only finitely many coordinates.
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  classical
  have hcoordinate : ∀ i, ∃ C : Set (X i),
      C ∈ 𝓝 (x i) ∧ IsConnected C ∧ (i ∈ (I : Set ι) → C ⊆ t i) := by
    intro i
    by_cases hi : i ∈ (I : Set ι)
    · obtain ⟨C, hC, hCpreconnected, hCt⟩ :=
        locallyConnectedSpace_iff_connected_subsets.mp inferInstance (x i) (t i) (ht i)
      exact ⟨C, hC, ⟨⟨x i, mem_of_mem_nhds hC⟩, hCpreconnected⟩,
        fun _ ↦ hCt⟩
    · exact ⟨univ, Filter.univ_mem, isConnected_univ, fun h ↦ (hi h).elim⟩
  choose C hCmem hCconnected hCsubset using hcoordinate
  refine ⟨(I : Set ι).pi C, set_pi_mem_nhds I.finite_toSet fun i _ ↦ hCmem i, ?_, ?_⟩
  -- Regard the cylinder as a full product, with unrestricted coordinates equal to `univ`.
  · rw [← Set.univ_pi_ite, isConnected_univ_pi]
    intro i
    by_cases hi : i ∈ (I : Set ι)
    · simpa only [if_pos hi] using hCconnected i
    · simp only [if_neg hi, isConnected_univ]
  · exact fun y hy ↦ htU fun i hi ↦ hCsubset i hi (hy i hi)

/-- Helper for Exercise 44.4: the countable power of the closed unit interval is weakly
locally connected. -/
instance instWeaklyLocallyConnectedSpaceHilbertCube :
    WeaklyLocallyConnectedSpace (ℕ → unitInterval) := by
  letI : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  exact weaklyLocallyConnectedSpacePiOfConnected
