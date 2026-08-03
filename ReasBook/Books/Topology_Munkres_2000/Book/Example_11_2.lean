module

public import Topology_Munkres_2000.Book.Example_11_2.HorizontalOrder

public section

open scoped HorizontalOrder

/- Example 11.2 (1): The strict horizontal-line order compares points of equal
height by their first coordinates. -/
#check (· ≺ ·)

/- Example 11.2 (2): The strict horizontal-line order is a strict partial
order on `ℝ × ℝ`. -/
#check HorizontalOrder.instIsStrictOrder

/- Example 11.2 (3): Two strictly comparable points lie on the same horizontal
line. -/
#check HorizontalOrder.comparable_sameHeight

/- Example 11.2 (4): The maximal simply ordered subsets are exactly the
horizontal lines in `ℝ × ℝ`. -/
namespace HorizontalOrder

/-- Example 11.2: The maximal chains for the strict horizontal-line order are
exactly the horizontal lines in `ℝ × ℝ`. -/
theorem isMaxChain_iff (s : Set (ℝ × ℝ)) :
    IsMaxChain (· ≺ ·) s ↔ ∃ y : ℝ, s = line y := by
  -- Apply the classification proved from the horizontal-line chain invariant.
  exact maximalChains_eq_horizontalLines s

end HorizontalOrder
