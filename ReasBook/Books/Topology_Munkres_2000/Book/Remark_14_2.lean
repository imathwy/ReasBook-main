module

public import Topology_Munkres_2000.Book.Definition_14_3.OrderBasis

public section

universe u

namespace OrderTopology

/-- Remark 14.2 (1): if the order has no smallest element, the interval basis has no
half-open intervals adjoining a least element. -/
@[simp]
theorem leftEndpointIntervals_eq_empty {α : Type u} [LinearOrder α] [NoMinOrder α] :
    leftEndpointIntervals α = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  rw [mem_leftEndpointIntervals] at hs
  obtain ⟨a₀, _, ha₀, _, _⟩ := hs
  obtain ⟨a, ha⟩ := exists_lt a₀
  exact (not_le_of_gt ha) (ha₀.2 (Set.mem_univ a))

/-- Remark 14.2 (2): if the order has no largest element, the interval basis has no
half-open intervals adjoining a greatest element. -/
@[simp]
theorem rightEndpointIntervals_eq_empty {α : Type u} [LinearOrder α] [NoMaxOrder α] :
    rightEndpointIntervals α = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  rw [mem_rightEndpointIntervals] at hs
  obtain ⟨_, b₀, hb₀, _, _⟩ := hs
  obtain ⟨b, hb⟩ := exists_gt b₀
  exact (not_le_of_gt hb) (hb₀.2 (Set.mem_univ b))

/-- If a linear order has neither endpoint, its interval basis consists exactly of open
intervals. -/
theorem basis_eq_openIntervals (α : Type u) [LinearOrder α] [NoMinOrder α] [NoMaxOrder α] :
    basis α = openIntervals α := by
  rw [basis_eq_union]
  simp

end OrderTopology
