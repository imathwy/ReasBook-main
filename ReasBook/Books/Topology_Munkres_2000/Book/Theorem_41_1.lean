module

public import Mathlib.Topology.Compactness.Paracompact

public section

/- Theorem 41.1. Every paracompact Hausdorff space `X` is normal; in mathlib,
Hausdorff spaces are `T2Space`s and normal spaces in the book's convention are
`T4Space`s. -/
#check T4Space.of_paracompactSpace_t2Space
