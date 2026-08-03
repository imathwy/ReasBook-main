module

public import Mathlib.Topology.Separation.Hausdorff

public section

open Filter
open scoped Topology

universe u

/- Theorem 17.10. If `X` is a Hausdorff space, then a sequence of points of `X`
converges to at most one point of `X`. -/
#check fun {X : Type u} [TopologicalSpace X] [T2Space X] (sequence : ℕ → X) {x y : X}
    (hx : Tendsto sequence atTop (𝓝 x)) (hy : Tendsto sequence atTop (𝓝 y)) ↦
  tendsto_nhds_unique hx hy
