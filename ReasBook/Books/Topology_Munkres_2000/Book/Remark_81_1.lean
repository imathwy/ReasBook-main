module

import Topology_Munkres_2000.Book.Assumption_81_1
import Topology_Munkres_2000.Book.Definition_81_1.CoveringTransformation
import Mathlib.GroupTheory.QuotientGroup.Basic

public section

open scoped CoveringTransformation

universe u v

/- Remark 81.1: The lifting correspondence of §54 and the existence of equivalences
proved in §79 will establish a correspondence between `H₀.normalizer / H₀` and the
group of covering transformations `𝒞(E, p, B)`. -/
#check CoveringTransformation.group

#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) ↦
  let H₀ := hp.fundamentalGroupMapRange he₀
  let N₀ := Subgroup.normalizer (H₀ : Set (FundamentalGroup B b₀))
  N₀ ⧸ H₀.subgroupOf N₀
