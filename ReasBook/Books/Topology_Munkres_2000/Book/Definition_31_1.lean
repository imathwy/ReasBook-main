module

import Mathlib.Topology.Separation.Hausdorff

/- Definition 31.1: A topological space `X` is Hausdorff if every pair of
distinct points of `X` lies in respective disjoint open sets. This is the
`T2Space X` property. -/
#check T2Space

-- The canonical characterization by disjoint open neighborhoods.
#check t2Space_iff
