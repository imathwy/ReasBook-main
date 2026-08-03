module

import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation

public section

open scoped CoveringTransformation

universe u v

/- Definition 81.1: Given a covering map `p : E → B`, the self-homeomorphisms of `E`
lying over `p` form the group of covering transformations `𝒞(E, p, B)`. -/
#check CoveringTransformation.group
#check fun {E : Type u} {B : Type v} [TopologicalSpace E] (p : E → B) ↦ 𝒞(E, p, B)
#check CoveringTransformation.mem_group
