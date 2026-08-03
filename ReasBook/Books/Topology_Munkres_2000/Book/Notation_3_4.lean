module

import Mathlib.Order.Defs.Unbundled

public section

universe u

variable {α : Type u} [LT α] [IsStrictTotalOrder α (· < ·)] (x y z : α)

/- Notation 3.4: The symbol `<` conventionally denotes a strict total order. -/
#check IsStrictTotalOrder
#check x < y

/- In this notation, distinct elements are comparable. -/
#check (fun (hxy : x ≠ y) ↦
  Or.elim (trichotomous x y) Or.inl fun h ↦
    Or.elim h (fun h ↦ (hxy h).elim) Or.inr : x ≠ y → x < y ∨ y < x)

/- A strict inequality implies that its endpoints are distinct. -/
#check fun (hxy : x < y) ↦ ne_of_irrefl hxy

/- Strict inequality is transitive. -/
#check fun (hxy : x < y) (hyz : y < z) ↦ IsTrans.trans x y z hxy hyz
