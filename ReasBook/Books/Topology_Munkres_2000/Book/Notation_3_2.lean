module

import Mathlib.Data.Rel

open scoped SetRel

universe u

variable {α : Type u} (r : SetRel α α) (x y z : α)

/- Notation 3.2. For an equivalence relation `r`, the notation `x ~[r] y`
expresses that `x` is related to `y`. In this notation, `Equivalence` states
reflexivity, symmetry, and transitivity. -/
#check x ~[r] y
#check fun (h : Equivalence (· ~[r] ·)) ↦ h.refl x
#check fun (h : Equivalence (· ~[r] ·)) (hxy : x ~[r] y) ↦ h.symm hxy
#check fun (h : Equivalence (· ~[r] ·))
    (hxy : x ~[r] y) (hyz : y ~[r] z) ↦ h.trans hxy hyz
