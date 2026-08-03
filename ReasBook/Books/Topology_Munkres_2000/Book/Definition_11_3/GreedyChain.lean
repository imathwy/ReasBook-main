module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.SetTheory.Cardinal.Order

public section

universe u v

namespace GreedyChain

open Classical in
/-- The greedy indicator associated to a well-ordered indexing of a relation.
An index is accepted exactly when its value is comparable with every earlier accepted value. -/
noncomputable def indicator {A : Type u} {J : Type v} (r : A → A → Prop)
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) : J → Fin 2 :=
  IsWellFounded.fix s fun α previous ↦
    if ∀ β : J, ∀ hβα : s β α,
      previous β hβα = 0 → Relation.SymmGen r (a α) (a β)
    then 0 else 1

/-- The recursive acceptance equation for `indicator`. -/
theorem indicator_eq_zero_iff {A : Type u} {J : Type v} (r : A → A → Prop)
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) (α : J) :
    indicator r s a α = 0 ↔
      ∀ β : J, s β α → indicator r s a β = 0 → Relation.SymmGen r (a α) (a β) := by
  -- Expose one recursive step, leaving every predecessor value in the canonical indicator form.
  unfold indicator
  rw [IsWellFounded.fix_eq]
  -- The indicator is zero exactly in the successful branch of its defining test.
  simp

/-- The recursive acceptance equation uniquely determines the greedy indicator. -/
theorem indicator_unique {A : Type u} {J : Type v} (r : A → A → Prop)
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) (h : J → Fin 2)
    (h_step : ∀ α : J,
      h α = 0 ↔ ∀ β : J, s β α → h β = 0 → Relation.SymmGen r (a α) (a β)) :
    h = indicator r s a := by
  -- Compare the two indicators pointwise by induction along the well-order.
  funext α
  apply IsWellFounded.induction s α
  intro α ih
  have hzero : h α = 0 ↔ indicator r s a α = 0 := by
    calc
      h α = 0 ↔ ∀ β : J, s β α → h β = 0 → Relation.SymmGen r (a α) (a β) :=
        h_step α
      _ ↔ ∀ β : J, s β α → indicator r s a β = 0 →
          Relation.SymmGen r (a α) (a β) := by
        constructor
        · intro hcomp β hβα hβ
          exact hcomp β hβα ((ih β hβα).symm ▸ hβ)
        · intro hcomp β hβα hβ
          exact hcomp β hβα ((ih β hβα) ▸ hβ)
      _ ↔ indicator r s a α = 0 := (indicator_eq_zero_iff r s a α).symm
  -- Elements of `Fin 2` are determined by whether they equal zero.
  omega

/-- The subset accepted by the greedy construction. -/
noncomputable def set {A : Type u} {J : Type v} (r : A → A → Prop)
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) : Set A :=
  a '' {α | indicator r s a α = 0}

/-- Membership in the greedy set is witnessed by an accepted index. -/
theorem mem_set {A : Type u} {J : Type v} (r : A → A → Prop)
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) (x : A) :
    x ∈ set r s a ↔ ∃ α : J, indicator r s a α = 0 ∧ a α = x := by
  -- Unpack image membership into an accepted index and its enumerated value.
  unfold set
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩

/-- A surjective well-ordered indexing produces a maximal chain. -/
theorem isMaxChain {A : Type u} {J : Type v} (r : A → A → Prop) [IsStrictOrder A r]
    (s : J → J → Prop) [IsWellOrder J s] (a : J → A) (ha : Function.Surjective a) :
    IsMaxChain r (set r s a) := by
  -- Every later accepted value was tested against every earlier accepted value.
  have hchain : IsChain r (set r s a) := by
    intro x hx y hy hxy
    rw [mem_set] at hx hy
    obtain ⟨α, hα, rfl⟩ := hx
    obtain ⟨β, hβ, rfl⟩ := hy
    have hαβ : α ≠ β := by
      intro h
      apply hxy
      rw [h]
    obtain hαβ | heq | hβα := trichotomous_of s α β
    · exact Or.symm ((indicator_eq_zero_iff r s a β).mp hβ α hαβ hα)
    · exact (hαβ heq).elim
    · exact (indicator_eq_zero_iff r s a α).mp hα β hβα hβ
  refine ⟨hchain, ?_⟩
  intro t ht hsub
  apply Set.Subset.antisymm hsub
  intro x hx
  obtain ⟨α, rfl⟩ := ha x
  by_contra hnot
  have hα : indicator r s a α ≠ 0 := by
    intro hα
    exact hnot ((mem_set r s a (a α)).mpr ⟨α, hα, rfl⟩)
  -- Rejection supplies an earlier accepted value incomparable with the rejected one.
  have hnotComparable : ¬∀ β : J, s β α → indicator r s a β = 0 →
      Relation.SymmGen r (a α) (a β) := by
    intro hcomp
    exact hα ((indicator_eq_zero_iff r s a α).mpr hcomp)
  push Not at hnotComparable
  obtain ⟨β, hβα, hβ, hinc⟩ := hnotComparable
  have haβ : a β ∈ t := hsub ((mem_set r s a (a β)).mpr ⟨β, hβ, rfl⟩)
  have hne : a α ≠ a β := by
    intro h
    apply hnot
    exact (mem_set r s a (a α)).mpr ⟨β, hβ, h.symm⟩
  -- A larger chain would make the rejected value comparable with that predecessor.
  exact hinc (ht hx haβ hne)


end GreedyChain

end
