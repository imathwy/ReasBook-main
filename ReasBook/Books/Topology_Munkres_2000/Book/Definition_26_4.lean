module

import Topology_Munkres_2000.Book.Definition_26_4.Tube

universe u v

/- Definition 26.4. A tube about the slice through `x₀` is a set of the form
`W ×ˢ (Set.univ : Set Y)`, where `W` is an open neighborhood of `x₀`. -/
#check (Set.IsTubeAbout : {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → X → Set (X × Y) → Prop)

#check Set.IsTubeAbout.prod_univ
#check Set.IsTubeAbout.slice_subset
