module

public import Topology_Munkres_2000.Book.Definition_8_99_3.PruferManifold

public section

/- Definition 8.99.3: The union of the positive-`x` half-plane at height zero and
one nonpositive-`x` half-plane at every real height, equipped with the topology generated
by the three basis families from Exercise 8.99.6, is called the Prüfer manifold. -/
#check PruferManifold
#check PruferManifold.basis
#check PruferManifold.instTopologicalSpace

namespace PruferManifold

/-- Definition 8.99.3: The designated sets form a topological basis for the Prüfer manifold. -/
theorem basis_isTopologicalBasis : TopologicalSpace.IsTopologicalBasis basis := by
  -- Refine intersections separately on the negative region, boundary, and positive region.
  refine ⟨?_, sUnion_basis_eq_univ, topology_eq_generateFrom⟩
  intro s hs t ht p hp
  rcases lt_trichotomy p.x 0 with hx | hx | hx
  · obtain ⟨U, hUOpen, hpU, hUbasis, hUs⟩ :=
      exists_sheetInteriorOpen_subset_of_mem_basis hs hp.1 hx
    obtain ⟨V, hVOpen, hpV, hVbasis, hVt⟩ :=
      exists_sheetInteriorOpen_subset_of_mem_basis ht hp.2 hx
    refine ⟨sheetInteriorOpen p.z (U ∩ V),
      mem_basis_iff.mpr (Or.inr (Or.inl ⟨p.z, U ∩ V, hUOpen.inter hVOpen, rfl⟩)), ?_, ?_⟩
    · exact mem_sheetInteriorOpen_iff.mpr ⟨rfl, hx, ⟨hpU, hpV⟩⟩
    · intro q hq
      exact ⟨hUs (mem_sheetInteriorOpen_iff.mpr
        ⟨(mem_sheetInteriorOpen_iff.mp hq).1, (mem_sheetInteriorOpen_iff.mp hq).2.1,
          (mem_sheetInteriorOpen_iff.mp hq).2.2.1⟩),
        hVt (mem_sheetInteriorOpen_iff.mpr
          ⟨(mem_sheetInteriorOpen_iff.mp hq).1, (mem_sheetInteriorOpen_iff.mp hq).2.1,
            (mem_sheetInteriorOpen_iff.mp hq).2.2.2⟩)⟩
  · obtain ⟨a, b, ε, hab, hε, hpG, hG⟩ :=
      exists_gluingNeighborhood_subset_inter_of_x_eq_zero hs ht hp hx
    exact ⟨gluingNeighborhood p.z a b ε,
      mem_basis_iff.mpr (Or.inr (Or.inr ⟨p.z, a, b, ε, hab, hε, rfl⟩)), hpG, hG⟩
  · obtain ⟨U, hUOpen, hpU, hUbasis, hUs⟩ :=
      exists_upperOpen_subset_of_mem_basis hs hp.1 hx
    obtain ⟨V, hVOpen, hpV, hVbasis, hVt⟩ :=
      exists_upperOpen_subset_of_mem_basis ht hp.2 hx
    refine ⟨upperOpen (U ∩ V),
      mem_basis_iff.mpr (Or.inl ⟨U ∩ V, hUOpen.inter hVOpen, rfl⟩), ?_, ?_⟩
    · exact mem_upperOpen_iff.mpr ⟨hx, ⟨hpU, hpV⟩⟩
    · intro q hq
      exact ⟨hUs (mem_upperOpen_iff.mpr
        ⟨(mem_upperOpen_iff.mp hq).1, (mem_upperOpen_iff.mp hq).2.1⟩),
        hVt (mem_upperOpen_iff.mpr
          ⟨(mem_upperOpen_iff.mp hq).1, (mem_upperOpen_iff.mp hq).2.2⟩)⟩

end PruferManifold
