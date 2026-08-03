module

import Mathlib.Topology.MetricSpace.Isometry

universe u

variable {X : Type u} [MetricSpace X] (f : X → X)

/- Definition 28.5: A self-map `f : X → X` of a metric space is an isometry when
`dist (f x) (f y) = dist x y` for all `x y : X`. -/
#check (Isometry f)
#check (isometry_iff_dist_eq : Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y)
