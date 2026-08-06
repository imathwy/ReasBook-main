module

public import Mathlib.Topology.Homotopy.Path

public section

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Definition 1.2.1: Two paths from `x` to `y` are equivalent when they are homotopic through
paths from `x` to `y`, so the endpoints remain fixed throughout the homotopy. -/
#check (Path.Homotopic : Path x y → Path x y → Prop)
