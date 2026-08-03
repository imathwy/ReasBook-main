module

public import Topology_Munkres_2000.Book.Theorem_20_2

public section

universe u

/- Example 21.2: For an uncountable index type `J`, the product topology on `J → ℝ`
is not metrizable. -/
#check fun (J : Type u) [Uncountable J]
    (h : TopologicalSpace.MetrizableSpace (J → ℝ)) ↦
  not_countable ((Pi.real_product_metrizable_iff_countable J).mp h)
