module

public import Topology_Munkres_2000.Book.Example_13_2.RectangularRegions

public section

namespace EuclideanPlane

/-- Example 13.2: The axis-parallel open rectangular regions form a basis for the
Euclidean plane. -/
theorem isTopologicalBasis_rectangularRegions :
    TopologicalSpace.IsTopologicalBasis rectangularRegions := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · -- Every member is open because it is represented by an open rectangle.
    intro U hU
    obtain ⟨a, b, c, d, _, _, rfl⟩ := (mem_rectangularRegions U).mp hU
    exact isOpen_openRectangle a b c d
  · intro x U hx hU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    let V := openRectangle (x 0 - r / 3) (x 0 + r / 3)
      (x 1 - r / 3) (x 1 + r / 3)
    -- The centered rectangle contains `x` and has strictly ordered bounds.
    have hxV : x ∈ V := by
      simp only [V, mem_openRectangle]
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · linarith
      · linarith
    have hVmem : V ∈ rectangularRegions := by
      rw [mem_rectangularRegions]
      use x 0 - r / 3, x 0 + r / 3, x 1 - r / 3, x 1 + r / 3
      constructor
      · linarith
      constructor
      · linarith
      · rfl
    -- Containment in the metric ball places the rectangle inside `U`.
    refine ⟨V, hVmem, hxV, ?_⟩
    exact (openRectangle_centered_subset_ball x hr).trans hball

end EuclideanPlane
