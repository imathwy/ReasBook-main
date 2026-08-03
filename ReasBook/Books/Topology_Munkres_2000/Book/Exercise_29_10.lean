module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Mathlib.Topology.Separation.Hausdorff

public section

open Set Filter Topology

universe u

/-- Exercise 29.10: In a Hausdorff space, every neighborhood of a weakly locally
compact point contains the compact closure of another neighborhood of that point. -/
theorem exists_nhds_isCompact_closure_subset {X : Type u}
    [TopologicalSpace X] [T2Space X] {x : X}
    (hcompact : IsWeaklyLocallyCompactAt x) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V : Set X, V ∈ 𝓝 x ∧ IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨K, hKcompact, hKx⟩ := isWeaklyLocallyCompactAt_iff.mp hcompact
  obtain ⟨V, ⟨hVx, hVcompact, hVclosed⟩, hVU⟩ :=
    (hKcompact.isCompact_isClosed_basis_nhds hKx).mem_iff.mp hU
  refine ⟨V, hVx, ?_, ?_⟩
  · rwa [hVclosed.closure_eq]
  · rwa [hVclosed.closure_eq]
