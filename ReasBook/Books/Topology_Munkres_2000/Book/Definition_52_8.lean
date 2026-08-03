module

import Mathlib.Topology.Homotopy.Path

@[expose] public section

universe u v

/- Definition 52.8: A continuous map `h : C(X, Y)` carrying `x₀` to `y₀` sends a
loop `f : Path x₀ x₀` to the loop represented by the composite `h ∘ f`, based at
`h x₀` (which is `y₀`). -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X, Y)) (x₀ : X) (f : Path x₀ x₀) ↦ f.map h.continuous
