module

import Mathlib.Data.Rel
import Mathlib.Logic.Relator

universe u v

open scoped SetRel

/- Definition 2.2: A rule of assignment from `C` to `D` is a subset of
`C × D` that relates each element of `C` to at most one element of `D`. -/
#check fun {C : Type u} {D : Type v} (r : SetRel C D) ↦
  Relator.RightUnique fun c d ↦ c ~[r] d
