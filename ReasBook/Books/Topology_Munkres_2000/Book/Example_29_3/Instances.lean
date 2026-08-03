module

public import Mathlib.Topology.Order.Compact

public section

open Set Filter

universe u

/-- An ordered topological space with compact closed intervals is weakly locally compact. -/
instance instWeaklyLocallyCompactSpaceOfCompactIccSpace (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [CompactIccSpace X] :
    WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x := by
    by_cases h_min : IsMin x
    · by_cases h_max : IsMax x
      · refine ⟨Icc x x, isCompact_Icc, mem_of_superset univ_mem ?_⟩
        intro y _
        exact ⟨(le_total x y).elim id fun hyx ↦ h_min hyx,
          (le_total y x).elim id fun hxy ↦ h_max hxy⟩
      · obtain ⟨y, hy⟩ := not_isMax_iff.mp h_max
        refine ⟨Icc x y, isCompact_Icc, mem_of_superset (Iic_mem_nhds hy) ?_⟩
        intro z hz
        exact ⟨(le_total x z).elim id fun hzx ↦ h_min hzx, hz⟩
    · obtain ⟨z, hz⟩ := not_isMin_iff.mp h_min
      by_cases h_max : IsMax x
      · refine ⟨Icc z x, isCompact_Icc, mem_of_superset (Ici_mem_nhds hz) ?_⟩
        intro y hy
        exact ⟨hy, (le_total y x).elim id fun hxy ↦ h_max hxy⟩
      · obtain ⟨y, hy⟩ := not_isMax_iff.mp h_max
        exact ⟨Icc z y, isCompact_Icc, Icc_mem_nhds hz hy⟩
