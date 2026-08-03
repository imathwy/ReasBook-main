module

import Topology_Munkres_2000.Book.Definition_41_8.Refinement

public section

open Set

universe u v

variable {ι : Type v} {X : Type u} [TopologicalSpace X]
variable (V U : ι → Set X)

/- Definition 41.8: The condition `closure (V α) ⊆ U α` for each `α` says that
the family of closures of `V` is a precise refinement of the family `U`. -/
#check IsPreciseRefinement (fun α ↦ closure (V α)) U
