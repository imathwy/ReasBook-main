module

public import Mathlib.Order.RelIso.Set

public section

universe u

namespace Subrel

/-- A strict total order restricts to a strict total order on every subtype. -/
instance instIsStrictTotalOrderSubtype {α : Type u} (r : α → α → Prop)
    [IsStrictTotalOrder α r] (p : α → Prop) :
    IsStrictTotalOrder (Subtype p) (Subrel r p) where

end Subrel
