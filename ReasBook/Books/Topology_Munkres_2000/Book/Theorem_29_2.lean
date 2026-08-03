module

public import Mathlib.Topology.Separation.Hausdorff

public section

open Set Filter Topology

universe u

/-- Theorem 29.2: A Hausdorff space is weakly locally compact if and only if
every neighborhood contains the compact closure of a smaller neighborhood. -/
theorem weaklyLocallyCompactSpace_iff_exists_nhds_isCompact_closure_subset
    {X : Type u} [TopologicalSpace X] [T2Space X] :
    WeaklyLocallyCompactSpace X ↔
      ∀ (x : X) U, U ∈ 𝓝 x → ∃ V ∈ 𝓝 x, IsCompact (closure V) ∧ closure V ⊆ U := by
  constructor
  · intro hX x U hU
    -- Refine a compact neighborhood to a compact closed one lying inside `U`.
    obtain ⟨K, hKcompact, hKx⟩ := hX.exists_compact_mem_nhds x
    obtain ⟨V, ⟨hVx, hVcompact, hVclosed⟩, hVU⟩ :=
      (hKcompact.isCompact_isClosed_basis_nhds hKx).mem_iff.mp hU
    refine ⟨V, hVx, ?_, ?_⟩
    · rwa [hVclosed.closure_eq]
    · rwa [hVclosed.closure_eq]
  · intro h
    -- A compact closure supplied inside `univ` is itself a compact neighborhood.
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨V, hVx, hVcompact, _⟩ := h x univ univ_mem
    exact ⟨closure V, hVcompact, mem_of_superset hVx subset_closure⟩
