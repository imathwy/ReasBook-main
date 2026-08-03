module

import Topology_Munkres_2000.Book.Definition_26_1.Cover

/- Definition 26.3. If `Y` is a subspace of `X`, represented by its underlying
subset, then a collection `𝒜` of subsets of `X` covers `Y` when `Y ⊆ ⋃₀ 𝒜`. -/
#check Set.covers

/- Equivalently, every point of `Y` lies in a member of `𝒜`. -/
#check Set.covers_iff
