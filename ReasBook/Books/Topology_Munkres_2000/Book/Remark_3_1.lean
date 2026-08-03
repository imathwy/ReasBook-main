module

import Mathlib.Data.Setoid.Basic

universe u

/- Remark 3.1: The equivalence class determined by `x` contains `x`, since
`r x x`. -/
#check fun {A : Type u} (r : Setoid A) (x : A) ↦
  (r.refl' x : x ∈ {y | r y x})
