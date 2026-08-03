module

import Mathlib.Order.SetNotation

/- Remark 1.6 (1): For a collection `𝒜` of sets, `⋃₀ 𝒜` consists of the
elements belonging to at least one member of `𝒜`. -/
#check Set.sUnion
#check Set.mem_sUnion

/- Remark 1.6 (2): For a collection `𝒜` of sets, `⋂₀ 𝒜` consists of the
elements belonging to every member of `𝒜`. -/
#check Set.sInter
#check Set.mem_sInter
