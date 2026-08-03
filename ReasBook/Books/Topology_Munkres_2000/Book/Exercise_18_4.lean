module

public import Mathlib.Topology.Constructions.SumProd

public section

/- Exercise 18.4 (1). Given `y₀ : Y`, the map `fun x : X ↦ (x, y₀)` from `X` to
`X × Y` is a topological embedding.
-/
#check isEmbedding_prodMkLeft

/- Exercise 18.4 (2). Given `x₀ : X`, the map `Prod.mk x₀` from `Y` to `X × Y` is
a topological embedding.
-/
#check isEmbedding_prodMkRight
