module

public import Topology_Munkres_2000.Book.Example_13_2
public import Topology_Munkres_2000.Book.Example_15_1.ProductCoordinates

public section

namespace RealPlane

open EuclideanPlane

/-- The rectangular basis of Example 13.2, expressed in the product coordinates `ℝ × ℝ`. -/
def openRectangles : Set (Set (ℝ × ℝ)) :=
  Set.preimage productHomeomorph.symm '' rectangularRegions

/-- Membership in `openRectangles` is witnessed by four strictly ordered real endpoints. -/
@[simp] theorem mem_openRectangles (s : Set (ℝ × ℝ)) :
    s ∈ openRectangles ↔
      ∃ a b c d : ℝ, a < b ∧ c < d ∧ s = Set.Ioo a b ×ˢ Set.Ioo c d := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨a, b, c, d, hab, hcd, rfl⟩ :=
      mem_rectangularRegions _ |>.mp hU
    refine ⟨a, b, c, d, hab, hcd, ?_⟩
    ext x
    simp
    tauto
  · rintro ⟨a, b, c, d, hab, hcd, rfl⟩
    refine ⟨openRectangle a b c d, ?_, ?_⟩
    · exact mem_rectangularRegions _ |>.mpr ⟨a, b, c, d, hab, hcd, rfl⟩
    ext x
    simp
    tauto

/-- Example 15.1: The rectangular basis of Example 13.2 is also a basis for the standard product
topology on `ℝ × ℝ`. -/
theorem isTopologicalBasis_openRectangles :
    TopologicalSpace.IsTopologicalBasis openRectangles :=
  isTopologicalBasis_rectangularRegions.isInducing productHomeomorph.symm.isInducing

end RealPlane
