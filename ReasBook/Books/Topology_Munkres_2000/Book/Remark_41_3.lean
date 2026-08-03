module

public import Topology_Munkres_2000.Book.Remark_41_3.Paracompact

universe u

public section

open Set Filter Topology
open scoped Pointwise

namespace IsTopologicalGroup

/-- Remark 41.3. A locally compact T₁ topological group is paracompact, without any
connectedness assumption. -/
instance paracompactSpace (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [T1Space G] [LocallyCompactSpace G] :
    ParacompactSpace G := by
  -- Generate an open σ-compact subgroup from a compact identity neighborhood.
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H : Subgroup G := Subgroup.closure (K ∪ K⁻¹)
  have hKH : K ⊆ H := fun x hx ↦ Subgroup.subset_closure (Or.inl hx)
  have hHnhds : (H : Set G) ∈ 𝓝 (1 : G) := Filter.mem_of_superset hKnhds hKH
  have hHopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hHnhds
  have hHclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hHopen
  letI : WeaklyLocallyCompactSpace H := hHclosed.weaklyLocallyCompactSpace
  letI : SigmaCompactSpace H :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_subgroupClosure_of_isCompact_mem_nhds K hKcompact hKnhds)
  letI : ParacompactSpace H := paracompact_of_locallyCompact_sigmaCompact
  -- Every coset is homeomorphic to `H`, so their topological sum is paracompact.
  letI (q : G ⧸ H) : ParacompactSpace (q.out • (H : Set G) : Set G) := by
    let e := (Homeomorph.mulLeft q.out).image (H : Set G)
    have himage : Homeomorph.mulLeft q.out '' (H : Set G) = q.out • (H : Set G) := by
      rfl
    exact (e.trans (Homeomorph.setCongr himage)).paracompactSpace_iff.mp inferInstance
  letI : ParacompactSpace (Σ q : G ⧸ H, (q.out • (H : Set G) : Set G)) :=
    paracompactSpace_sigma
  exact (sigmaLeftCosetHomeomorph H hHopen).paracompactSpace_iff.mp inferInstance

end IsTopologicalGroup
