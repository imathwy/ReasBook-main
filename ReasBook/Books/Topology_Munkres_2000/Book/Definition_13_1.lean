module

import Mathlib.Topology.Bases

/-
Definition 13.1. A basis for a topology is represented by
`TopologicalSpace.IsTopologicalBasis`. Its fields express that the basis covers
the space and refines intersections at each point; the remaining checks expose
the generated topology, the pointwise characterization of open sets, and the
openness of basis elements.
-/
#check TopologicalSpace.IsTopologicalBasis
#check TopologicalSpace.IsTopologicalBasis.sUnion_eq
#check TopologicalSpace.IsTopologicalBasis.exists_subset_inter
#check TopologicalSpace.IsTopologicalBasis.eq_generateFrom
#check TopologicalSpace.IsTopologicalBasis.isOpen_iff
#check TopologicalSpace.IsTopologicalBasis.isOpen
