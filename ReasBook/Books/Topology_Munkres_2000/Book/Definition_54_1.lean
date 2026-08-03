module

public import Topology_Munkres_2000.Book.Definition_54_1.Lifting

public section

/- Definition 54.1. A lifting of `f : C(X, B)` through `p : E → B` is a continuous map
`lift : C(X, E)` satisfying `p ∘ lift = f`. -/
#check ContinuousMap.IsLift
