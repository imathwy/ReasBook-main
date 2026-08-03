module

import Mathlib.Data.Set.Lattice

universe u v

/- Notation 5.1: For an indexed family `A : J → Set X`, the notation
`⋃ α, A α` and `⋂ α, A α` denotes its indexed union and intersection.
Membership means belonging to at least one, respectively every, `A α`, and
these sets equal the union and intersection of the collection `Set.range A`. -/
#check fun {X : Type u} {J : Type v} (A : J → Set X) ↦ ⋃ α, A α
#check fun {X : Type u} {J : Type v} (A : J → Set X) ↦ ⋂ α, A α
#check Set.iUnion
#check Set.mem_iUnion
#check Set.iInter
#check Set.mem_iInter
#check Set.sUnion_range
#check Set.sInter_range
