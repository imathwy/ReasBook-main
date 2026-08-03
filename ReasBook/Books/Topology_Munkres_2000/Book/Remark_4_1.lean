module

public import Topology_Munkres_2000.Book.Assumption_4_1

public section

/-- Remark 4.1. In an ordered field, the arithmetic mean of two distinct
ordered elements lies strictly between them. -/
theorem arithmeticMean_mem_Ioo {K : Type u} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {x y : K} (hxy : x < y) :
    (x + y) / 2 ∈ Set.Ioo x y :=
  ⟨left_lt_add_div_two.mpr hxy, add_div_two_lt_right.mpr hxy⟩
