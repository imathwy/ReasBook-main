module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap

public section

open Function

namespace Circle

/-- Theorem 53.1: The map `Circle.turnExp : ℝ → Circle` is a covering map in
Munkres' sense: it satisfies mathlib's `IsCoveringMap` predicate and is surjective. -/
theorem turnExp_isCoveringMap :
    IsCoveringMap turnExp ∧ Surjective turnExp := by
  -- Combine the local-homeomorphism covering property with surjectivity.
  exact ⟨isCoveringMap_turnExp, turnExp_surjective⟩

end Circle

/- Each integer unit interval maps onto the circle under `Circle.turnExp`. -/
#check Circle.surjOn_Icc_int_turnExp
