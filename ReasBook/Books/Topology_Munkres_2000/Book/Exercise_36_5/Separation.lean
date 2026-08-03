module

public import Topology_Munkres_2000.Book.Exercise_36_5.Charts
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace LineWithTwoOrigins

/-- The line with two origins is not Hausdorff. -/
theorem notHausdorff : ¬ T2Space LineWithTwoOrigins := by
  intro hT2
  letI : T2Space LineWithTwoOrigins := hT2
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ :=
    t2_separation (show origin .p ≠ origin .q by simp)
  obtain ⟨bu, hbu, hpbu, hbuu⟩ :=
    basis_isTopologicalBasis.isOpen_iff.mp hu (origin .p) hpu
  obtain ⟨bv, hbv, hqbv, hbvv⟩ :=
    basis_isTopologicalBasis.isOpen_iff.mp hv (origin .q) hqv
  rcases mem_basis_iff.mp hbu with ⟨l, r, hlr, hzero, rfl⟩ | ⟨ou, a, ha, rfl⟩
  · exact (origin_not_mem_interval .p l r hpbu).elim
  · rcases mem_basis_iff.mp hbv with ⟨l, r, hlr, hzero, rfl⟩ | ⟨ov, b, hb, rfl⟩
    · exact (origin_not_mem_interval .q l r hqbv).elim
    · have hou : ou = .p := by
        rcases mem_originNeighborhood_iff.mp hpbu with hpbu | hpbu
        · exact (origin_not_mem_interval .p (-a) a hpbu).elim
        · exact origin.inj hpbu.symm
      have hov : ov = .q := by
        rcases mem_originNeighborhood_iff.mp hqbv with hqbv | hqbv
        · exact (origin_not_mem_interval .q (-b) b hqbv).elim
        · exact origin.inj hqbv.symm
      let c := min a b / 2
      have hc : 0 < c := div_pos (lt_min ha hb) (by norm_num)
      have hcu : point c hc.ne' ∈ originNeighborhood ou a := by
        rw [hou]
        exact mem_originNeighborhood_iff.mpr (.inl
          ((point_mem_interval_iff hc.ne').mpr
            ⟨by linarith, by dsimp [c]; linarith [min_le_left a b]⟩))
      have hcv : point c hc.ne' ∈ originNeighborhood ov b := by
        rw [hov]
        exact mem_originNeighborhood_iff.mpr (.inl
          ((point_mem_interval_iff hc.ne').mpr
            ⟨by linarith, by dsimp [c]; linarith [min_le_right a b]⟩))
      exact Set.disjoint_left.mp huv (hbuu hcu) (hbvv hcv)

end LineWithTwoOrigins
