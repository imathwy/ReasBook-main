module

import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

public section

/-
Definition 69.2. A family indexed by `ι` is a system of free generators for a
group `G` precisely when it is represented by `FreeGroupBasis ι G`, whose
coercion gives the family `ι → G`. The property that `G` admits such a system is
`IsFreeGroup G`, and `FreeGroupBasis.isFreeGroup` supplies this implication.
-/
#check FreeGroupBasis
#check IsFreeGroup
#check FreeGroupBasis.isFreeGroup
