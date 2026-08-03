module

import Mathlib.Data.Rel

universe u

open scoped SetRel

/- Notation 3.1: If `C` is a relation on `A`, then `x ~[C] y` means
`(x, y) ∈ C`, read as “`x` is in the relation `C` to `y`.” -/
#check fun {A : Type u} (C : SetRel A A) (x y : A) ↦ x ~[C] y
