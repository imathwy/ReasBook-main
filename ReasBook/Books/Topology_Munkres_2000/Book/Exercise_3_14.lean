module

public import Mathlib.Logic.Relation
public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty

public section

universe u

/-- Exercise 3.14 (1): A relation is symmetric if and only if it equals its
converse relation. -/
theorem symm_iff_eq_swap {α : Type u} (C : α → α → Prop) :
    Std.Symm C ↔ C = Function.swap C := by
  rw [eq_comm]
  exact swap_eq_iff.symm

section

variable {α : Type u} (C : α → α → Prop) [IsStrictTotalOrder α C]

/- Exercise 3.14 (2): The converse of a strict total order is a strict total
order. -/
#check (inferInstance : IsStrictTotalOrder α (Function.swap C))

end


/-- Exercise 3.14 (3): If a linear order has the greatest lower bound property,
then it has the least upper bound property. -/
theorem greatestLowerBoundProperty_implies_leastUpperBoundProperty
    (α : Type u) [LinearOrder α] (h : GreatestLowerBoundProperty α) :
    LeastUpperBoundProperty α := by
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro s hs hb
  obtain ⟨a, ha⟩ := h.exists_isGLB (upperBounds s) hb hs.bddBelow_upperBounds
  exact ⟨a, isGLB_upperBounds.mp ha⟩
