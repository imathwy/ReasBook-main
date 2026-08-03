module

public import Mathlib.Order.Bounds.Basic

public section

open Set

universe u

/-- A linear order has the least upper bound property when each nonempty subset
that is bounded above has a least upper bound. -/
class LeastUpperBoundProperty (α : Type u) [LinearOrder α] : Prop where
  /-- Every nonempty bounded-above set has a least upper bound. -/
  exists_isLUB (s : Set α) (hs : s.Nonempty) (hb : BddAbove s) : ∃ a, IsLUB s a

/-- A linear order has the least upper bound property if every nonempty
bounded-above set has a least upper bound. -/
theorem LeastUpperBoundProperty.of_exists_isLUB {α : Type u} [LinearOrder α]
    (h : ∀ s : Set α, s.Nonempty → BddAbove s → ∃ a, IsLUB s a) :
    LeastUpperBoundProperty α := ⟨h⟩

/-- A linear order has the greatest lower bound property when each nonempty subset
that is bounded below has a greatest lower bound. -/
def GreatestLowerBoundProperty (α : Type u) [LinearOrder α] : Prop :=
  ∀ s : Set α, s.Nonempty → BddBelow s → ∃ a, IsGLB s a

/-- A nonempty bounded-below set in a linear order with the greatest lower bound
property has a greatest lower bound. -/
theorem GreatestLowerBoundProperty.exists_isGLB {α : Type u} [LinearOrder α]
    (h : GreatestLowerBoundProperty α) (s : Set α) (hs : s.Nonempty)
    (hb : BddBelow s) : ∃ a, IsGLB s a :=
  h s hs hb

/-- A linear order has the greatest lower bound property if every nonempty
bounded-below set has a greatest lower bound. -/
theorem GreatestLowerBoundProperty.of_exists_isGLB {α : Type u} [LinearOrder α]
    (h : ∀ s : Set α, s.Nonempty → BddBelow s → ∃ a, IsGLB s a) :
    GreatestLowerBoundProperty α :=
  h
