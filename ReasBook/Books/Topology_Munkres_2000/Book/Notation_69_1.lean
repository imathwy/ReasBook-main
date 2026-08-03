module

import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-
Notation 69.1. For the free group `FreeGroup J`, the book's generator `a_α` is
represented by `FreeGroup.of α`. The canonical basis
`FreeGroupBasis.ofFreeGroup J` records this family as a system of free
generators.
-/
#check FreeGroup.of
#check FreeGroupBasis.ofFreeGroup
#check FreeGroupBasis.ofFreeGroup_apply
