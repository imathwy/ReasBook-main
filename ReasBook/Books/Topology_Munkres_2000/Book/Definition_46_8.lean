module

public import Topology_Munkres_2000.Book.Definition_46_8.Currying

public section

/-
Definition 46.8. A function `f : X × Z → Y` whose `X`-slices are continuous
induces a function `Z → C(X, Y)` by `F z x = f (x, z)`. Conversely, a function
`F : Z → C(X, Y)` determines a function `X × Z → Y` by the same equation. These
constructions form an equivalence.
-/
#check ContinuousMap.curryRightEquiv
#check ContinuousMap.curryRight
#check ContinuousMap.curryRight_apply
#check ContinuousMap.uncurryRight
#check ContinuousMap.uncurryRight_apply
#check ContinuousMap.continuous_uncurryRight_slice
#check ContinuousMap.uncurryRight_curryRight
#check ContinuousMap.curryRight_uncurryRight
