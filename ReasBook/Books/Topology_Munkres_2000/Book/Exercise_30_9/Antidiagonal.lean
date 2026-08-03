module

public import Topology_Munkres_2000.Book.Exercise_16_8.AffineLine

public section

open Set

namespace SorgenfreyPlane

/-- The antidiagonal in the Sorgenfrey plane. -/
def antiDiagonal : Set (SorgenfreyLine × SorgenfreyLine) :=
  {point | SorgenfreyLine.toReal point.2 = -SorgenfreyLine.toReal point.1}

/-- The antidiagonal point with real parameter `x`. -/
def antiDiagonalPoint (x : ℝ) : SorgenfreyLine × SorgenfreyLine :=
  (SorgenfreyLine.toReal.symm x, SorgenfreyLine.toReal.symm (-x))

/-- Membership in the antidiagonal is the coordinate equation `y = -x`. -/
theorem mem_antiDiagonal_iff (point : SorgenfreyLine × SorgenfreyLine) :
    point ∈ antiDiagonal ↔
      SorgenfreyLine.toReal point.2 = -SorgenfreyLine.toReal point.1 := Iff.rfl

/-- Every point supplied by the standard parameterization lies on the antidiagonal. -/
theorem antiDiagonalPoint_mem (x : ℝ) : antiDiagonalPoint x ∈ antiDiagonal := by
  simp [antiDiagonal, antiDiagonalPoint]

/-- The standard parameterization has exactly the antidiagonal as its range. -/
theorem range_antiDiagonalPoint : range antiDiagonalPoint = antiDiagonal := by
  ext point
  constructor
  · rintro ⟨x, rfl⟩
    exact antiDiagonalPoint_mem x
  · intro hpoint
    refine ⟨SorgenfreyLine.toReal point.1, ?_⟩
    apply Prod.ext
    · simp [antiDiagonalPoint]
    · apply SorgenfreyLine.toReal.injective
      simpa [antiDiagonalPoint] using (mem_antiDiagonal_iff point).mp hpoint |>.symm

/-- The antidiagonal is the affine graph line of slope `-1` through the origin. -/
theorem antiDiagonal_eq_graphLine : antiDiagonal = SorgenfreyAffineLine.graph (-1) 0 := by
  ext point
  rw [mem_antiDiagonal_iff, SorgenfreyAffineLine.mem_graph_iff]
  ring_nf

end SorgenfreyPlane
