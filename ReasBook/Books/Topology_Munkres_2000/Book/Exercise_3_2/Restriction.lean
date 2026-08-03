module

public import Mathlib.Order.RelIso.Set

public section

universe u

namespace Equivalence

/-- An equivalence relation restricts to an equivalence relation on any subtype. -/
protected theorem subrel {A : Type u} {C : A → A → Prop} (hC : Equivalence C)
    (p : A → Prop) : Equivalence (Subrel C p) where
  refl x := hC.refl x.1
  symm hxy := hC.symm hxy
  trans hxy hyz := hC.trans hxy hyz

end Equivalence
