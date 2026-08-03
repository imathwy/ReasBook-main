module

import Init

universe u v

/- Notation 2.1: The notation `f : A → B` says that `f` is a function with
domain `A` and codomain `B`. Munkres calls `B` the range here; this is the
specified target, not the image `Set.range f`. When `A` and `B` are sets, Lean
uses their subtype carriers as the domain and codomain types. -/
#check fun {A : Type u} {B : Type v} (f : A → B) ↦ f
