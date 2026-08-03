module

import Mathlib.Topology.Homotopy.Basic

/- Definition 46.10: For a homotopy `F : f₀.Homotopy f₁`, the curried map
`F.curry : C(unitInterval, C(X, Y))` is the continuous one-parameter family of
maps from `X` to `Y`, beginning at `f₀` and ending at `f₁`. -/
#check ContinuousMap.Homotopy.curry
#check ContinuousMap.Homotopy.curry_apply
#check ContinuousMap.Homotopy.curry_zero
#check ContinuousMap.Homotopy.curry_one
