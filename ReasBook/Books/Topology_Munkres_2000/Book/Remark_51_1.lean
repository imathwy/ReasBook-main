module

import Mathlib.Topology.Homotopy.Basic

/- Remark 51.1. For a homotopy `F : f.Homotopy f'`, the curried map
`F.curry : C(unitInterval, C(X, Y))` is the continuous one-parameter family of
maps from `X` to `Y`: at time `t` it is the map `x ↦ F (t, x)`, it begins at
`f`, and it ends at `f'`. -/
#check ContinuousMap.Homotopy.curry
#check ContinuousMap.Homotopy.curry_apply
#check ContinuousMap.Homotopy.curry_zero
#check ContinuousMap.Homotopy.curry_one
