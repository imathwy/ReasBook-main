module

public import Mathlib.Topology.Separation.Hausdorff

public section

universe u v

/- Exercise 3.99.5. If `X` is a Hausdorff space, then a net in `X` converges to
at most one point of `X`. -/
#check fun {J : Type u} {X : Type v} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] [T2Space X] (net : J → X) {x y : X}
    (hx : Filter.Tendsto net Filter.atTop (nhds x))
    (hy : Filter.Tendsto net Filter.atTop (nhds y)) ↦ tendsto_nhds_unique hx hy
