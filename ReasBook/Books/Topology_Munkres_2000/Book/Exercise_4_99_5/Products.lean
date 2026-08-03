module

public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Topology.Connected.LocallyPathConnected

public section

universe u v

/-- A finite product of locally connected spaces is locally connected. -/
instance Pi.locallyConnectedSpace_of_finite {ι : Type u} {X : ι → Type v} [Finite ι]
    [∀ i, TopologicalSpace (X i)] [∀ i, LocallyConnectedSpace (X i)] :
    LocallyConnectedSpace (∀ i, X i) := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, _hIFinite, t, ht, hIU⟩ := hU
  -- Refine every coordinate neighborhood to an open connected neighborhood.
  choose s hs using fun i ↦
    (LocallyConnectedSpace.open_connected_basis (x i)).mem_iff.mp (ht i)
  refine ⟨Set.univ.pi s, ?_, ?_, ?_, ?_⟩
  · exact (Set.pi_mono' (fun i _ ↦ (hs i).2) (Set.subset_univ I)).trans hIU
  · exact isOpen_set_pi Set.finite_univ fun i _ ↦ (hs i).1.1
  · exact fun i _ ↦ (hs i).1.2.1
  · exact isConnected_univ_pi.mpr fun i ↦ (hs i).1.2.2

/-- A finite product of locally path-connected spaces is locally path-connected. -/
instance Pi.locallyPathConnectedSpace_of_finite {ι : Type u} {X : ι → Type v} [Finite ι]
    [∀ i, TopologicalSpace (X i)] [∀ i, LocallyPathConnectedSpace (X i)] :
    LocallyPathConnectedSpace (∀ i, X i) := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, _hIFinite, t, ht, hIU⟩ := hU
  -- Refine every coordinate neighborhood to a path-connected neighborhood.
  choose s hs using fun i ↦
    (path_connected_basis (x i)).mem_iff.mp (ht i)
  refine ⟨Set.univ.pi s, ?_, IsPathConnected.pi (fun i ↦ (hs i).1.2), ?_⟩
  · exact set_pi_mem_nhds Set.finite_univ fun i _ ↦ (hs i).1.1
  · exact (Set.pi_mono' (fun i _ ↦ (hs i).2) (Set.subset_univ I)).trans hIU

/-- A finite product of locally metrizable spaces is locally metrizable. -/
instance Pi.locallyMetrizableSpace_of_finite {ι : Type u} {X : ι → Type v} [Finite ι]
    [∀ i, TopologicalSpace (X i)] [∀ i, LocallyMetrizableSpace (X i)] :
    LocallyMetrizableSpace (∀ i, X i) := by
  rw [locallyMetrizableSpace_iff]
  intro x
  -- Take metrizable coordinate neighborhoods and form their finite cylinder.
  choose s hsNhds hsMetrizable using fun i ↦
    LocallyMetrizableSpace.exists_metrizable_nhds (x i)
  refine ⟨Set.univ.pi s, set_pi_mem_nhds Set.finite_univ (fun i _ ↦ hsNhds i), ?_⟩
  letI : ∀ i, TopologicalSpace.MetrizableSpace (s i) := hsMetrizable
  have hContinuous : Continuous (Equiv.Set.univPi s) := by
    exact continuous_pi fun i ↦
      ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hContinuousSymm : Continuous (Equiv.Set.univPi s).symm := by
    exact (continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
  exact ((Equiv.Set.univPi s).isHomeomorph_iff.mpr
    ⟨hContinuous, hContinuousSymm⟩).isEmbedding.metrizableSpace
