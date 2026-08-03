module

public import Topology_Munkres_2000.Book.Theorem_8_1.LeastUnused
public import Mathlib.Order.InitialSeg

public section

open scoped InitialSeg

universe u v

/-- An initial-segment embedding satisfies the least-unused recursion. -/
theorem InitialSeg.isLeastUnused
    {J : Type u} {C : Type v} [LinearOrder J] [LinearOrder C]
    (h : J ≤i C) : Function.IsLeastUnused h := by
  apply Function.IsLeastUnused.of_forall
  intro x
  constructor
  · refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨y, hy, hxy⟩
    exact hy.ne (h.injective hxy)
  · intro c hc
    apply le_of_not_gt
    intro hcx
    apply hc.2
    obtain ⟨y, hy⟩ := h.mem_range_of_rel hcx
    exact ⟨y, h.map_rel_iff.mp (hy ▸ hcx), hy⟩

end
