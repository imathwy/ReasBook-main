import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u}

/- Definition 1.1.8: for an equivalence relation `r` on `S`, the equivalence classes are the
subsets in `Setoid.classes r`, i.e. the subsets of the form `{ y | r y x }`; any element of such a
subset is a representative of that class. -/
recall Setoid.classes (r : Setoid S) : Set (Set S)

namespace Setoid

/-- Any element of an equivalence class is a representative that recovers the same class. -/
theorem eq_setOf_rel_of_mem_classes {r : Setoid S} {C : Set S} (hC : C ∈ r.classes) {x : S}
    (hx : x ∈ C) : C = { y | r y x } :=
  Setoid.eq_of_mem_classes hC hx (r.mem_classes x) (r.refl' x)

end Setoid
