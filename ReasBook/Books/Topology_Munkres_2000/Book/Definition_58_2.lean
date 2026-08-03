module

public import Mathlib.Topology.Homotopy.Equiv

public section

/- Definition 58.2. A homotopy equivalence from `X` to `Y` consists of continuous maps
`f : C(X, Y)` and `g : C(Y, X)` such that `g.comp f` is homotopic to `ContinuousMap.id X` and
`f.comp g` is homotopic to `ContinuousMap.id Y`. The maps are homotopy inverses of each other. -/
#check ContinuousMap.HomotopyEquiv
#check ContinuousMap.HomotopyEquiv.mk
