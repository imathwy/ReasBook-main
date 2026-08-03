module

public import Mathlib.Order.WellFounded

public section

universe u

namespace Set

/-- Helper for Exercise 10.7: a subset of an ordered type is inductive if it
contains each element whenever it contains every strict predecessor of that element. -/
def IsInductive {J : Type u} [LT J] (J₀ : Set J) : Prop :=
  ∀ α : J, {β : J | β < α} ⊆ J₀ → α ∈ J₀

namespace IsInductive

/-- An inductive subset of a well-founded ordered type is the whole type. -/
theorem eq_univ {J : Type u} [LT J] [WellFoundedLT J] {J₀ : Set J}
    (hJ₀ : J₀.IsInductive) : J₀ = Set.univ := by
  -- It suffices to prove membership of each element by induction on its predecessors.
  refine Set.eq_univ_iff_forall.mpr fun α ↦ ?_
  refine wellFounded_lt.induction α ?_
  intro γ hγ
  -- The induction hypotheses say exactly that every strict predecessor lies in `J₀`.
  exact hJ₀ γ fun β hβγ ↦ hγ β hβγ

end IsInductive

end Set

/-- Exercise 10.7 (2). The principle of transfinite induction: an inductive
subset of a well-ordered type is the whole type. -/
theorem transfiniteInductionPrinciple {J : Type u} [LinearOrder J] [WellFoundedLT J]
    (J₀ : Set J) (hJ₀ : J₀.IsInductive) : J₀ = Set.univ := by
  -- Apply the relation-level induction theorem to the strict order of `J`.
  exact Set.IsInductive.eq_univ hJ₀
