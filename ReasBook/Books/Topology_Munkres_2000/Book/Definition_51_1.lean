module

public import Mathlib.Topology.Homotopy.Contractible

public section

/-
Definition 51.1. A homotopy from `f` to `f'` is a continuous map on
`unitInterval × X` whose restrictions at `0` and `1` are `f` and `f'`.
Mathlib places the interval coordinate first, rather than using the source's
equivalent order `X × unitInterval`. The relations `ContinuousMap.Homotopic`
and `ContinuousMap.Nullhomotopic` express homotopy and nullhomotopy.
-/
#check ContinuousMap.Homotopy
#check ContinuousMap.Homotopy.mk
#check ContinuousMap.Homotopy.apply_zero
#check ContinuousMap.Homotopy.apply_one
#check ContinuousMap.Homotopic
#check ContinuousMap.Nullhomotopic
