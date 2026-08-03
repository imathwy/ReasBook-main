module

public import Topology_Munkres_2000.Book.Exercise_13_8.RationalIntervals

public section

namespace RealPlane

/-- The collection of open rectangles in `ℝ × ℝ` whose four endpoints are rational. -/
def rationalOpenRectangles : Set (Set (ℝ × ℝ)) :=
  Set.image2 (· ×ˢ ·) Real.rationalOpenIntervals Real.rationalOpenIntervals

/-- Membership in `rationalOpenRectangles` is witnessed by four ordered rational endpoints. -/
theorem mem_rationalOpenRectangles (s : Set (ℝ × ℝ)) :
    s ∈ rationalOpenRectangles ↔ ∃ a b c d : ℚ, a < b ∧ c < d ∧
      s = Set.Ioo (a : ℝ) (b : ℝ) ×ˢ Set.Ioo (c : ℝ) (d : ℝ) := by
  simp only [rationalOpenRectangles, Set.mem_image2, Real.mem_rationalOpenIntervals]
  aesop

/-- Exercise 16.6 (1): The collection of rational-endpoint open rectangles is countable. -/
theorem rationalOpenRectangles_countable : rationalOpenRectangles.Countable :=
  Real.rationalOpenIntervals_countable.image2 Real.rationalOpenIntervals_countable (· ×ˢ ·)

/-- Exercise 16.6 (2): The rational-endpoint open rectangles form a basis for `ℝ × ℝ`. -/
theorem rationalOpenRectangles_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis rationalOpenRectangles :=
  Real.rationalOpenIntervals_isTopologicalBasis.prod
    Real.rationalOpenIntervals_isTopologicalBasis

end RealPlane
