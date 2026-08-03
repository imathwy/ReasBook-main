module

public import Mathlib.Topology.Constructions.SumProd

public section

universe u v w

/- Exercise 3.99.4: If two nets with the same directed index set converge to
`x : X` and `y : Y`, then their paired net converges to `(x, y)` in `X × Y`. -/
#check fun {J : Type u} {X : Type v} {Y : Type w} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] [TopologicalSpace Y]
    (xNet : J → X) (yNet : J → Y) (x : X) (y : Y)
    (hx : Filter.Tendsto xNet Filter.atTop (nhds x))
    (hy : Filter.Tendsto yNet Filter.atTop (nhds y)) ↦
  (hx.prodMk_nhds hy :
    Filter.Tendsto (fun α ↦ (xNet α, yNet α)) Filter.atTop (nhds (x, y)))
