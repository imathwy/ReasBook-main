module

public import Topology_Munkres_2000.Book.Algorithm_76_2.Cut

public section

/-
Definition 76.4: Cut replaces `y₀ y₁` by `y₀ c⁻¹` and `c y₁` when `c`
occurs nowhere else in the total labelling scheme and both fragments have length at least two.
-/
#check LabellingScheme.Cut.ofNegativePositive
