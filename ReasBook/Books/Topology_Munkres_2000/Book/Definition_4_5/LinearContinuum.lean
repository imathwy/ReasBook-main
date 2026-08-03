module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

universe u

/-- A linear continuum is a linearly ordered type that is densely ordered and has the
least upper bound property. -/
class LinearContinuum (α : Type u) [LinearOrder α] : Prop extends DenselyOrdered α where
  /-- Every nonempty subset that is bounded above has a least upper bound. -/
  leastUpperBoundProperty : LeastUpperBoundProperty α

namespace LinearContinuum

/-- A linear order is a linear continuum exactly when it has the least upper bound
property and is densely ordered. -/
theorem iff (α : Type u) [LinearOrder α] :
    LinearContinuum α ↔ LeastUpperBoundProperty α ∧ DenselyOrdered α := by
  constructor
  · exact fun h ↦ ⟨h.leastUpperBoundProperty, h.toDenselyOrdered⟩
  · exact fun h ↦ { h.2 with leastUpperBoundProperty := h.1 }

/-- Every conditionally complete densely ordered linear order is a linear continuum. -/
instance instOfConditionallyCompleteLinearOrder (α : Type u)
    [ConditionallyCompleteLinearOrder α] [DenselyOrdered α] : LinearContinuum α where
  leastUpperBoundProperty := LeastUpperBoundProperty.of_exists_isLUB fun s hs hb ↦
    ⟨sSup s, isLUB_csSup hs hb⟩

end LinearContinuum
