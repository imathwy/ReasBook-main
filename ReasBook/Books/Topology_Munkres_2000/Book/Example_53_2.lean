module

public import Topology_Munkres_2000.Book.Example_53_2.CircleMap

public section

/- Example 53.2 (1): The positive-real circle map is
`x ↦ (Real.cos (2 * Real.pi * x), Real.sin (2 * Real.pi * x))`. -/
#check Circle.coe_positiveRealExp

/- The positive-real circle map is the restriction of the one-turn circle map. -/
#check Circle.positiveRealExp_apply

/- Example 53.2 (2): The positive-real circle map is surjective. -/
#check Circle.positiveRealExp_surjective

/- Example 53.2 (3): The positive-real circle map is a local homeomorphism. -/
#check Circle.positiveRealExp_isLocalHomeomorph

/- Example 53.2 (4): The point `(1 : Circle)` has no evenly covered neighborhood. -/
#check Circle.positiveRealExp_not_isEvenlyCovered_one

namespace Circle

/-- Example 53.2 (5): The positive-real circle map is not a covering map. -/
theorem positiveRealExp_not_isCoveringMap : ¬ IsCoveringMap positiveRealExp := by
  -- A covering map would evenly cover the basepoint `1 : Circle`.
  intro hCovering
  exact positiveRealExp_not_isEvenlyCovered_one (hCovering 1)

end Circle
