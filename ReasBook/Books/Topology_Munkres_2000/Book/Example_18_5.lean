module

public import Topology_Munkres_2000.Book.Example_3_9.OrderIso
public import Mathlib.Topology.Order.MonotoneContinuity

public section

/- Example 18.5: The order isomorphism `openUnitIntervalOrderIso`, whose forward map is
`x ↦ x / (1 - x ^ 2)` and whose inverse is
`y ↦ 2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2))`, is a homeomorphism from
`Set.Ioo (-1 : ℝ) 1` to `ℝ`. -/
#check openUnitIntervalOrderIso.toHomeomorph
