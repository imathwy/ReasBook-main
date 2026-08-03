module

import Mathlib.Data.Rel

universe u v

/- Definition 2.5: If `f : A → B` and `a : A`, then `f a` is the value of
`f` at `a`, also called the image of `a` under `f`. -/
#check fun {α : Type u} {β : Type v} (A : Set α) (B : Set β)
    (f : A → B) (a : A) ↦ f a

-- Membership in the graph of `f` is equivalent to having value `f a`.
#check Function.mem_graph
