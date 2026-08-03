module

import Mathlib.Data.Setoid.Partition

universe u

/- Definition 3.4: For a setoid `r` on `A` and `x : A`, the equivalence class
determined by `x` is the subset `{y | r y x}` of `A`. -/
#check fun {A : Type u} (r : Setoid A) (x : A) ↦ ({y | r y x} : Set A)

/- The equivalence class determined by an element belongs to the setoid's
collection of equivalence classes. -/
#check Setoid.mem_classes
