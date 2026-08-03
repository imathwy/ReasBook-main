module

import Init

universe u v w

/- Definition 18.7: For `f : A → X × Y`, the maps `Prod.fst ∘ f` and
`Prod.snd ∘ f` are called the coordinate functions of `f`. -/
#check fun {A : Type u} {X : Type v} {Y : Type w} (f : A → X × Y) ↦
  Prod.fst ∘ f
#check fun {A : Type u} {X : Type v} {Y : Type w} (f : A → X × Y) ↦
  Prod.snd ∘ f
