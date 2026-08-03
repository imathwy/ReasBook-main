module

public import Mathlib.Topology.«Homotopy».Basic

public section

/-
Definition 46.9. A homotopy from `f` to `g` is a continuous map on
`unitInterval × X` whose restrictions at `0` and `1` are `f` and `g`.
Mathlib places the interval coordinate first, rather than using the source's
equivalent order `X × unitInterval`.
-/
#check ContinuousMap.Homotopy
#check ContinuousMap.Homotopy.mk
#check ContinuousMap.Homotopy.apply_zero
#check ContinuousMap.Homotopy.apply_one
#check ContinuousMap.Homotopic
