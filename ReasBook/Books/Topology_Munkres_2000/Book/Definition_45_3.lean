module

public import Mathlib.Topology.Bornology.Constructions

public section

universe u v w

/-- Definition 45.3. A set of function-like maps is pointwise bounded when the set of its values
at each point is bounded. -/
protected abbrev Set.PointwiseBounded {F : Type w} {X : Type u} {Y : Type v}
    [CoeFun F (fun _ ↦ X → Y)] [Bornology Y] (𝓕 : Set F) : Prop :=
  ∀ x, Bornology.IsBounded ((fun f : F ↦ f x) '' 𝓕)
