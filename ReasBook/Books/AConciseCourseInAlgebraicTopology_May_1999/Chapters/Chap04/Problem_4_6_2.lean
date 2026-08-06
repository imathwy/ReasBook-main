module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Index

public section

universe u

-- Semantic recall via `lean_leansearch`: `IsFreeGroup`, `Subgroup.not_finiteIndex_iff`,
-- `Subgroup.index_eq_zero_iff_infinite`, and `Group.fg_iff_subgroup_fg` are the canonical
-- free-group, infinite-index, and finite-generation APIs underlying this problem statement.

variable {F : Type u} [Group F] [IsFreeGroup F] (N : Subgroup F) [N.Normal]

/-- Problem 4.6.2: a nontrivial normal subgroup `N` of a free group `F` cannot be finitely
generated when `N` has infinite index in `F`, expressed canonically as `¬ N.FiniteIndex`. -/
theorem normalSubgroup_not_fg_of_not_finiteIndex
    (hN : N ≠ ⊥) (hindex : ¬ N.FiniteIndex) :
    ¬ N.FG := sorry

/-- Bridge form of `normalSubgroup_not_fg_of_not_finiteIndex`, using mathlib's index convention
`N.index = 0` for infinite index. -/
theorem normalSubgroup_not_fg_of_index_eq_zero
    (hN : N ≠ ⊥) (hindex : N.index = 0) :
    ¬ N.FG := by
  exact normalSubgroup_not_fg_of_not_finiteIndex N hN (N.not_finiteIndex_iff.2 hindex)

/-- Quotient form of `normalSubgroup_not_fg_of_not_finiteIndex`, using the canonical equivalence
`N.index = 0 ↔ Infinite (F ⧸ N)`. -/
theorem normalSubgroup_not_fg_of_infinite_quotient
    (hN : N ≠ ⊥) (hquot : Infinite (F ⧸ N)) :
    ¬ N.FG := by
  exact normalSubgroup_not_fg_of_index_eq_zero N hN (N.index_eq_zero_iff_infinite.2 hquot)
