module

public import Topology_Munkres_2000.Book.Example_3_7.SquareOrder

@[expose] public section

/- Example 3.7 (1): The usual relation `(· < ·)` is a strict total order on `ℝ`. -/
#check (inferInstance : IsStrictTotalOrder ℝ (· < ·))

/- Example 3.7 (2): The relation `squareLexLt` is a strict total order on `ℝ`. -/
#check (inferInstance : IsStrictTotalOrder ℝ squareLexLt)
