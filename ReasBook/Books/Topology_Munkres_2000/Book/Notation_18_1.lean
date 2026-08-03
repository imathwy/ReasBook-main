module

import Mathlib.Data.Set.Image

universe u v

/- Notation 18.1: For `f : X → Y` and `V : Set Y`, the preimage `f ⁻¹' V`
consists of the points `x : X` such that `f x ∈ V`. Munkres's image set
`f(X)` is `Set.range f`, so the preimage is empty exactly when `V` is
disjoint from `Set.range f`. -/
#check fun {X : Type u} {Y : Type v} (f : X → Y) (V : Set Y) ↦
  (f ⁻¹' V : Set X)

#check Set.mem_preimage
#check Set.preimage_eq_empty_iff
